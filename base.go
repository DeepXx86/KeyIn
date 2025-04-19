package main

import (
	"archive/zip"
	"bufio"
	"bytes"
	"crypto/cipher"
	"crypto/hmac"
	"crypto/rand"
	"crypto/subtle"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"hash"
	"io"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"time"

	"github.com/enceve/crypto/serpent"
	"github.com/vivint/infectious"
	"golang.org/x/crypto/argon2"
	"golang.org/x/crypto/blake2b"
	"golang.org/x/crypto/chacha20"
	"golang.org/x/crypto/hkdf"
	"golang.org/x/crypto/sha3"
	"golang.org/x/term"
)

var KiB = 1 << 10
var MiB = 1 << 20
var GiB = 1 << 30
var TiB = 1 << 40

var version = "v1.0"

type Config struct {
	Paranoid       bool   `json:"paranoid"`
	ReedSolomon    bool   `json:"reed_solomon"`
	Deniability    bool   `json:"deniability"`
	Recursively    bool   `json:"recursively"`
	Split          bool   `json:"split"`
	SplitSize      string `json:"split_size"`
	SplitUnit      string `json:"split_unit"`
	Compress       bool   `json:"compress"`
	Delete         bool   `json:"delete"`
	AutoUnzip      bool   `json:"auto_unzip"`
	SameLevel      bool   `json:"same_level"`
	Keep           bool   `json:"keep"`
	KeyfileOrdered bool   `json:"keyfile_ordered"`
}

var defaultConfig = Config{
	Paranoid:       false,
	ReedSolomon:    false,
	Deniability:    false,
	Recursively:    false,
	Split:          false,
	SplitSize:      "",
	SplitUnit:      "MiB",
	Compress:       false,
	Delete:         false,
	AutoUnzip:      false,
	SameLevel:      false,
	Keep:           false,
	KeyfileOrdered: false,
}

var config Config
var mode string
var working bool
var inputFile string
var inputFileOld string
var outputFile string
var password string
var comments string
var keyfile bool
var keyfiles []string
var kept bool
var recombine bool

var rs1, _ = infectious.NewFEC(1, 3)
var rs5, _ = infectious.NewFEC(5, 15)
var rs16, _ = infectious.NewFEC(16, 48)
var rs24, _ = infectious.NewFEC(24, 72)
var rs32, _ = infectious.NewFEC(32, 96)
var rs64, _ = infectious.NewFEC(64, 192)
var rs128, _ = infectious.NewFEC(128, 136)
var fastDecode bool

var compressDone int64
var compressTotal int64
var compressStart time.Time
var padded bool

var lastProgressUpdate time.Time
var progressInterval = 500 * time.Millisecond

func loadConfig(configPath string) error {
	config = defaultConfig

	if _, err := os.Stat(configPath); err == nil {
		data, err := os.ReadFile(configPath)
		if err != nil {
			return err
		}

		return json.Unmarshal(data, &config)
	}

	return saveConfig(configPath)
}

func saveConfig(configPath string) error {
	data, err := json.MarshalIndent(config, "", "  ")
	if err != nil {
		return err
	}

	return os.WriteFile(configPath, data, 0644)
}

func printProgress(done int64, total int64, start time.Time, status string) {

	if time.Since(lastProgressUpdate) < progressInterval {
		return
	}
	lastProgressUpdate = time.Now()

	progress, speed, eta := statify(done, total, start)
	progressPercent := progress * 100

	fmt.Printf("\r\033[K%s: %.2f%% at %.2f MiB/s (ETA: %s)", status, progressPercent, speed, eta)
}

func work(encryptMode bool) error {
	fmt.Println("Starting operation...")
	working = true

	var salt []byte
	var hkdfSalt []byte
	var serpentIV []byte
	var nonce []byte
	var keyHash []byte
	var keyHashRef []byte
	var keyfileKey []byte
	var keyfileHash = make([]byte, 32)
	var keyfileHashRef []byte
	var authTag []byte

	if len(keyfiles) > 0 {
		fmt.Println("Processing keyfiles...")

		var keyfileTotal int64
		for _, path := range keyfiles {
			stat, _ := os.Stat(path)
			keyfileTotal += stat.Size()
		}

		if config.KeyfileOrdered {
			var tmp = sha3.New256()
			var keyfileDone int

			for _, path := range keyfiles {
				fin, _ := os.Open(path)
				for {
					data := make([]byte, MiB)
					size, err := fin.Read(data)
					if err != nil {
						break
					}
					data = data[:size]
					tmp.Write(data)

					keyfileDone += size
					progress := float32(keyfileDone) / float32(keyfileTotal)
					fmt.Printf("\rReading keyfiles: %.2f%%", progress*100)
				}
				fin.Close()
			}
			fmt.Println()
			keyfileKey = tmp.Sum(nil)

			tmp = sha3.New256()
			tmp.Write(keyfileKey)
			keyfileHash = tmp.Sum(nil)
		} else {
			var keyfileDone int

			for _, path := range keyfiles {
				fin, _ := os.Open(path)
				tmp := sha3.New256()
				for {
					data := make([]byte, MiB)
					size, err := fin.Read(data)
					if err != nil {
						break
					}
					data = data[:size]
					tmp.Write(data)

					keyfileDone += size
					progress := float32(keyfileDone) / float32(keyfileTotal)
					fmt.Printf("\rReading keyfiles: %.2f%%", progress*100)
				}
				fin.Close()

				sum := tmp.Sum(nil)

				if keyfileKey == nil {
					keyfileKey = sum
				} else {
					for i, j := range sum {
						keyfileKey[i] ^= j
					}
				}
			}
			fmt.Println()

			tmp := sha3.New256()
			tmp.Write(keyfileKey)
			keyfileHash = tmp.Sum(nil)
		}
	}

	fin, err := os.Open(inputFile)
	if err != nil {
		return fmt.Errorf("Failed to open input file: %v", err)
	}
	defer fin.Close()

	var fout *os.File

	stat, _ := os.Stat(inputFile)
	total := stat.Size()

	if encryptMode {
		fmt.Println("Preparing encryption...")

		if _, err := os.Stat(outputFile); err == nil && !config.Split {
			return fmt.Errorf("Output file %s already exists", outputFile)
		}

		fout, err = os.Create(outputFile)
		if err != nil {
			return fmt.Errorf("Failed to create output file: %v", err)
		}
		defer fout.Close()

		salt = make([]byte, 16)
		hkdfSalt = make([]byte, 32)
		serpentIV = make([]byte, 16)
		nonce = make([]byte, 24)

		errs := make([]error, 11)

		_, errs[0] = fout.Write(rsEncode(rs5, []byte(version)))

		if len(comments) > 99999 {
			return errors.New("comments exceed maximum length")
		}

		commentsLength := []byte(fmt.Sprintf("%05d", len(comments)))
		_, errs[1] = fout.Write(rsEncode(rs5, commentsLength))

		for _, i := range []byte(comments) {
			_, err := fout.Write(rsEncode(rs1, []byte{i}))
			if err != nil {
				errs[2] = err
			}
		}

		flags := make([]byte, 5)
		if config.Paranoid {
			flags[0] = 1
		}
		if len(keyfiles) > 0 {
			flags[1] = 1
		}
		if config.KeyfileOrdered {
			flags[2] = 1
		}
		if config.ReedSolomon {
			flags[3] = 1
		}
		if total%int64(MiB) >= int64(MiB)-128 {
			flags[4] = 1
		}
		_, errs[3] = fout.Write(rsEncode(rs5, flags))

		if _, err := rand.Read(salt); err != nil {
			return fmt.Errorf("Failed to generate random salt: %v", err)
		}
		if _, err := rand.Read(hkdfSalt); err != nil {
			return fmt.Errorf("Failed to generate HKDF salt: %v", err)
		}
		if _, err := rand.Read(serpentIV); err != nil {
			return fmt.Errorf("Failed to generate Serpent IV: %v", err)
		}
		if _, err := rand.Read(nonce); err != nil {
			return fmt.Errorf("Failed to generate ChaCha20 nonce: %v", err)
		}

		_, errs[4] = fout.Write(rsEncode(rs16, salt))
		_, errs[5] = fout.Write(rsEncode(rs32, hkdfSalt))
		_, errs[6] = fout.Write(rsEncode(rs16, serpentIV))
		_, errs[7] = fout.Write(rsEncode(rs24, nonce))

		_, errs[8] = fout.Write(make([]byte, 192))
		_, errs[9] = fout.Write(make([]byte, 96))
		_, errs[10] = fout.Write(make([]byte, 192))

		for _, err := range errs {
			if err != nil {
				return fmt.Errorf("Error writing header: %v", err)
			}
		}

		if !encryptMode {
			total -= 789
			if len(comments) > 0 {
				total -= int64(len(comments) * 3)
			}
		}
	} else {
		fmt.Println("Preparing decryption...")

		errs := make([]error, 10)

		versionBytes := make([]byte, 15)
		fin.Read(versionBytes)
		versionBytes, errs[0] = rsDecode(rs5, versionBytes)

		commentLengthBytes := make([]byte, 15)
		fin.Read(commentLengthBytes)
		commentLengthBytes, errs[1] = rsDecode(rs5, commentLengthBytes)

		if valid, err := regexp.Match(`^\d{5}$`, commentLengthBytes); !valid || err != nil {
			return errors.New("Unable to read comments length")
		}

		commentsLength, _ := strconv.Atoi(string(commentLengthBytes))
		commentBytes := make([]byte, commentsLength*3)
		fin.Read(commentBytes)

		comments = ""
		for i := 0; i < commentsLength*3; i += 3 {
			t, err := rsDecode(rs1, commentBytes[i:i+3])
			if err != nil {
				comments = "Comments are corrupted"
				break
			}
			comments += string(t)
		}

		total -= int64(commentsLength) * 3

		flags := make([]byte, 15)
		fin.Read(flags)
		flags, errs[2] = rsDecode(rs5, flags)
		config.Paranoid = flags[0] == 1
		keyfile = flags[1] == 1
		config.KeyfileOrdered = flags[2] == 1
		config.ReedSolomon = flags[3] == 1
		padded = flags[4] == 1

		salt = make([]byte, 48)
		fin.Read(salt)
		salt, errs[3] = rsDecode(rs16, salt)

		hkdfSalt = make([]byte, 96)
		fin.Read(hkdfSalt)
		hkdfSalt, errs[4] = rsDecode(rs32, hkdfSalt)

		serpentIV = make([]byte, 48)
		fin.Read(serpentIV)
		serpentIV, errs[5] = rsDecode(rs16, serpentIV)

		nonce = make([]byte, 72)
		fin.Read(nonce)
		nonce, errs[6] = rsDecode(rs24, nonce)

		keyHashRef = make([]byte, 192)
		fin.Read(keyHashRef)
		keyHashRef, errs[7] = rsDecode(rs64, keyHashRef)

		keyfileHashRef = make([]byte, 96)
		fin.Read(keyfileHashRef)
		keyfileHashRef, errs[8] = rsDecode(rs32, keyfileHashRef)

		authTag = make([]byte, 192)
		fin.Read(authTag)
		authTag, errs[9] = rsDecode(rs64, authTag)

		for _, err := range errs {
			if err != nil && !config.Keep {
				return fmt.Errorf("Volume header is damaged: %v", err)
			} else if err != nil {
				kept = true
				fmt.Println("Warning: Volume header is damaged but continuing due to force decrypt option")
			}
		}

		fout, err = os.Create(outputFile)
		if err != nil {
			return fmt.Errorf("Failed to create output file: %v", err)
		}
		defer fout.Close()

		total -= 789
	}

	fmt.Println("Deriving encryption keys...")
	var key []byte
	if config.Paranoid {
		key = argon2.IDKey(
			[]byte(password),
			salt,
			8,
			1<<20,
			8,
			32,
		)
	} else {
		key = argon2.IDKey(
			[]byte(password),
			salt,
			4,
			1<<20,
			4,
			32,
		)
	}

	tmp := sha3.New512()
	tmp.Write(key)
	keyHash = tmp.Sum(nil)

	if !encryptMode {
		keyCorrect := subtle.ConstantTimeCompare(keyHash, keyHashRef) == 1
		keyfileCorrect := subtle.ConstantTimeCompare(keyfileHash, keyfileHashRef) == 1
		incorrect := !keyCorrect
		if keyfile || len(keyfiles) > 0 {
			incorrect = !keyCorrect || !keyfileCorrect
		}

		if incorrect && !config.Keep {
			if !keyCorrect {
				return errors.New("The provided password is incorrect")
			} else {
				if config.KeyfileOrdered {
					return errors.New("Incorrect keyfiles or ordering")
				} else {
					return errors.New("Incorrect keyfiles")
				}
			}
		} else if incorrect {
			kept = true
			fmt.Println("Warning: Password or keyfiles incorrect but continuing due to force decrypt option")
		}
	}

	if len(keyfiles) > 0 || keyfile {
		if bytes.Equal(keyfileKey, make([]byte, 32)) {
			return errors.New("Duplicate keyfiles detected")
		}

		tmpKey := key
		key = make([]byte, 32)
		for i := range key {
			key[i] = tmpKey[i] ^ keyfileKey[i]
		}
	}

	done, counter := 0, 0
	chacha, _ := chacha20.NewUnauthenticatedCipher(key, nonce)

	var mac hash.Hash
	subkey := make([]byte, 32)
	hkdf := hkdf.New(sha3.New256, key, hkdfSalt, nil)
	hkdf.Read(subkey)
	if config.Paranoid {
		mac = hmac.New(sha3.New512, subkey)
	} else {
		mac, _ = blake2b.New512(subkey)
	}

	serpentKey := make([]byte, 32)
	hkdf.Read(serpentKey)
	s, _ := serpent.NewCipher(serpentKey)
	serpent := cipher.NewCTR(s, serpentIV)

	fmt.Println("Processing data...")
	startTime := time.Now()
	lastProgressUpdate = time.Now()

	for {
		var src []byte
		if !encryptMode && config.ReedSolomon {
			src = make([]byte, MiB/128*136)
		} else {
			src = make([]byte, MiB)
		}
		size, err := fin.Read(src)
		if err != nil && err != io.EOF {
			return fmt.Errorf("Error reading data: %v", err)
		}
		if size == 0 {
			break
		}

		src = src[:size]
		dst := make([]byte, len(src))

		if encryptMode {
			if config.Paranoid {
				serpent.XORKeyStream(dst, src)
				copy(src, dst)
			}

			chacha.XORKeyStream(dst, src)
			mac.Write(dst)

			if config.ReedSolomon {
				copy(src, dst)
				dst = nil
				if len(src) == MiB {
					for i := 0; i < MiB; i += 128 {
						dst = append(dst, rsEncode(rs128, src[i:i+128])...)
					}
				} else {
					chunks := math.Floor(float64(len(src)) / 128)
					for i := 0; float64(i) < chunks; i++ {
						dst = append(dst, rsEncode(rs128, src[i*128:(i+1)*128])...)
					}

					dst = append(dst, rsEncode(rs128, pad(src[int(chunks*128):]))...)
				}
			}
		} else {
			if config.ReedSolomon {
				copy(dst, src)
				src = nil
				if len(dst) == MiB/128*136 {
					for i := 0; i < MiB/128*136; i += 136 {
						tmp, err := rsDecode(rs128, dst[i:i+136])
						if err != nil && !config.Keep {
							return errors.New("The input file is irrecoverably damaged")
						} else if err != nil {
							kept = true
						}
						if i == MiB/128*136-136 && done+MiB/128*136 >= int(total) && padded {
							tmp = unpad(tmp)
						}
						src = append(src, tmp...)
					}
				} else {
					chunks := len(dst)/136 - 1
					for i := 0; i < chunks; i++ {
						tmp, err := rsDecode(rs128, dst[i*136:(i+1)*136])
						if err != nil && !config.Keep {
							return errors.New("The input file is irrecoverably damaged")
						} else if err != nil {
							kept = true
						}
						src = append(src, tmp...)
					}

					tmp, err := rsDecode(rs128, dst[int(chunks)*136:])
					if err != nil && !config.Keep {
						return errors.New("The input file is irrecoverably damaged")
					} else if err != nil {
						kept = true
					}
					src = append(src, unpad(tmp)...)
				}
				dst = make([]byte, len(src))
			}

			mac.Write(src)
			chacha.XORKeyStream(dst, src)

			if config.Paranoid {
				copy(src, dst)
				serpent.XORKeyStream(dst, src)
			}
		}

		_, err = fout.Write(dst)
		if err != nil {
			return fmt.Errorf("Error writing data: %v", err)
		}

		if !encryptMode && config.ReedSolomon {
			done += MiB / 128 * 136
		} else {
			done += size
		}
		counter += size

		if encryptMode {
			printProgress(int64(done), total, startTime, "Encrypting")
		} else {
			printProgress(int64(done), total, startTime, "Decrypting")
		}

		if counter >= 60*GiB {
			nonce = make([]byte, 24)
			hkdf.Read(nonce)
			chacha, _ = chacha20.NewUnauthenticatedCipher(key, nonce)

			serpentIV = make([]byte, 16)
			hkdf.Read(serpentIV)
			serpent = cipher.NewCTR(s, serpentIV)

			counter = 0
		}
	}

	fmt.Println("\nFinalizing...")

	if encryptMode {
		fout.Seek(int64(309+len(comments)*3), 0)
		fout.Write(rsEncode(rs64, keyHash))
		fout.Write(rsEncode(rs32, keyfileHash))
		fout.Write(rsEncode(rs64, mac.Sum(nil)))
	} else {
		if subtle.ConstantTimeCompare(mac.Sum(nil), authTag) == 0 {
			if !config.Keep {
				return errors.New("The input file is damaged or modified")
			} else {
				kept = true
				fmt.Println("Warning: Authentication failed but continuing due to force decrypt option")
			}
		}
	}

	if encryptMode && config.Deniability {
		fmt.Println("Adding plausible deniability...")

		fin.Close()
		fout.Close()

		os.Rename(outputFile, outputFile+".tmp")
		fin, _ = os.Open(outputFile + ".tmp")
		fout, _ = os.Create(outputFile)
		defer fin.Close()
		defer fout.Close()

		salt := make([]byte, 16)
		nonce := make([]byte, 24)
		if _, err := rand.Read(salt); err != nil {
			return fmt.Errorf("Failed to generate random salt: %v", err)
		}
		if _, err := rand.Read(nonce); err != nil {
			return fmt.Errorf("Failed to generate nonce: %v", err)
		}
		fout.Write(salt)
		fout.Write(nonce)

		key := argon2.IDKey([]byte(password), salt, 4, 1<<20, 4, 32)
		chacha, _ := chacha20.NewUnauthenticatedCipher(key, nonce)

		stat, _ := os.Stat(outputFile + ".tmp")
		total := stat.Size()

		done, counter := 0, 0
		startTime = time.Now()
		lastProgressUpdate = time.Now()

		for {
			src := make([]byte, MiB)
			size, err := fin.Read(src)
			if err != nil && err != io.EOF {
				return fmt.Errorf("Error reading data: %v", err)
			}
			if size == 0 {
				break
			}

			src = src[:size]
			dst := make([]byte, len(src))
			chacha.XORKeyStream(dst, src)
			fout.Write(dst)

			done += size
			counter += size

			printProgress(int64(done), total, startTime, "Adding deniability")

			if counter >= 60*GiB {
				tmp := sha3.New256()
				tmp.Write(nonce)
				nonce = tmp.Sum(nil)[:24]
				chacha, _ = chacha20.NewUnauthenticatedCipher(key, nonce)
				counter = 0
			}
		}

		os.Remove(outputFile + ".tmp")
		fmt.Println("\nDeniability layer added")
	}

	if encryptMode && config.Split && config.SplitSize != "" {
		fmt.Println("\nSplitting into chunks...")

		fin.Close()
		fout.Close()

		chunkSize, err := strconv.Atoi(config.SplitSize)
		if err != nil {
			return fmt.Errorf("Invalid chunk size: %v", err)
		}

		switch config.SplitUnit {
		case "KiB":
			chunkSize *= KiB
		case "MiB":
			chunkSize *= MiB
		case "GiB":
			chunkSize *= GiB
		case "TiB":
			chunkSize *= TiB
		}

		stat, _ := os.Stat(outputFile)
		size := stat.Size()

		chunks := int(math.Ceil(float64(size) / float64(chunkSize)))

		fin, _ = os.Open(outputFile)
		defer fin.Close()

		names, _ := filepath.Glob(outputFile + ".*")
		for _, i := range names {
			os.Remove(i)
		}

		startTime = time.Now()
		lastProgressUpdate = time.Now()
		finishedBytes := 0

		for i := 0; i < chunks; i++ {
			chunkPath := fmt.Sprintf("%s.%d", outputFile, i)
			fout, _ := os.Create(chunkPath)

			bytesWritten := 0
			for bytesWritten < chunkSize {
				bufSize := MiB
				if bytesWritten+bufSize > chunkSize {
					bufSize = chunkSize - bytesWritten
				}

				buf := make([]byte, bufSize)
				read, err := fin.Read(buf)
				if err != nil && err != io.EOF {
					fout.Close()
					return fmt.Errorf("Error reading data for chunk %d: %v", i, err)
				}
				if read == 0 {
					break
				}

				_, err = fout.Write(buf[:read])
				if err != nil {
					fout.Close()
					return fmt.Errorf("Error writing to chunk %d: %v", i, err)
				}

				bytesWritten += read
				finishedBytes += read

				printProgress(int64(finishedBytes), size, startTime, "Splitting")

				if read < bufSize {
					break
				}
			}

			fout.Close()
			fmt.Printf("\rCreated chunk %d/%d", i+1, chunks)
		}

		os.Remove(outputFile)
		fmt.Println("\nFile split into", chunks, "chunks")
	}

	if !encryptMode && !kept && config.AutoUnzip && strings.HasSuffix(outputFile, ".zip") {
		fmt.Println("Auto-unzipping the file...")

		if err := unpackArchive(outputFile); err != nil {
			return fmt.Errorf("Failed to unzip: %v", err)
		}

		os.Remove(outputFile)
		fmt.Println("File successfully unzipped")
	}

	if config.Delete {
		if encryptMode {
			fmt.Println("Deleting original file...")
			os.Remove(inputFile)
		} else {
			fmt.Println("Deleting encrypted volume...")
			os.Remove(inputFile)
		}
	}

	if kept {
		fmt.Println("Warning: The file was processed with errors. Handle with caution.")
	}

	fmt.Println("Operation completed successfully!")
	return nil
}

func rsEncode(rs *infectious.FEC, data []byte) []byte {
	res := make([]byte, rs.Total())
	rs.Encode(data, func(s infectious.Share) {
		res[s.Number] = s.Data[0]
	})
	return res
}

func rsDecode(rs *infectious.FEC, data []byte) ([]byte, error) {
	if rs.Total() == 136 && fastDecode {
		return data[:128], nil
	}

	tmp := make([]infectious.Share, rs.Total())
	for i := 0; i < rs.Total(); i++ {
		tmp[i].Number = i
		tmp[i].Data = append(tmp[i].Data, data[i])
	}
	res, err := rs.Decode(nil, tmp)

	if err != nil {
		if rs.Total() == 136 {
			return data[:128], err
		}
		return data[:rs.Total()/3], err
	}

	return res, nil
}

func pad(data []byte) []byte {
	padLen := 128 - len(data)%128
	padding := bytes.Repeat([]byte{byte(padLen)}, padLen)
	return append(data, padding...)
}

func unpad(data []byte) []byte {
	padLen := int(data[127])
	return data[:128-padLen]
}

func genPassword(length int) string {
	const chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz1234567890-=_+!@#$^&()?<>"

	tmp := make([]byte, length)
	for i := 0; i < length; i++ {
		j, _ := rand.Int(rand.Reader, big.NewInt(int64(len(chars))))
		tmp[i] = chars[j.Int64()]
	}

	return string(tmp)
}

func statify(done int64, total int64, start time.Time) (float32, float64, string) {
	progress := float32(done) / float32(total)
	elapsed := float64(time.Since(start)) / float64(MiB) / 1000
	speed := float64(done) / elapsed / float64(MiB)
	eta := int(math.Floor(float64(total-done) / (speed * float64(MiB))))
	return float32(math.Min(float64(progress), 1)), speed, timeify(eta)
}

func timeify(seconds int) string {
	hours := int(math.Floor(float64(seconds) / 3600))
	seconds %= 3600
	minutes := int(math.Floor(float64(seconds) / 60))
	seconds %= 60
	hours = int(math.Max(float64(hours), 0))
	minutes = int(math.Max(float64(minutes), 0))
	seconds = int(math.Max(float64(seconds), 0))
	return fmt.Sprintf("%02d:%02d:%02d", hours, minutes, seconds)
}

func sizeify(size int64) string {
	if size >= int64(TiB) {
		return fmt.Sprintf("%.2f TiB", float64(size)/float64(TiB))
	} else if size >= int64(GiB) {
		return fmt.Sprintf("%.2f GiB", float64(size)/float64(GiB))
	} else if size >= int64(MiB) {
		return fmt.Sprintf("%.2f MiB", float64(size)/float64(MiB))
	} else {
		return fmt.Sprintf("%.2f KiB", float64(size)/float64(KiB))
	}
}

func unpackArchive(zipPath string) error {
	reader, err := zip.OpenReader(zipPath)
	if err != nil {
		return err
	}
	defer reader.Close()

	var totalSize int64
	for _, f := range reader.File {
		totalSize += int64(f.UncompressedSize64)
	}

	var extractDir string
	if config.SameLevel {
		extractDir = filepath.Dir(zipPath)
	} else {
		extractDir = filepath.Join(filepath.Dir(zipPath), strings.TrimSuffix(filepath.Base(zipPath), ".zip"))
	}

	for _, f := range reader.File {
		if strings.Contains(f.Name, "..") {
			return errors.New("potentially malicious zip item path")
		}

		outPath := filepath.Join(extractDir, f.Name)

		if f.FileInfo().IsDir() {
			if err := os.MkdirAll(outPath, f.Mode()); err != nil {
				return err
			}
		}
	}

	var done int64
	startTime := time.Now()
	lastProgressUpdate = time.Now()

	for i, f := range reader.File {
		if f.FileInfo().IsDir() {
			continue
		}

		outPath := filepath.Join(extractDir, f.Name)

		if err := os.MkdirAll(filepath.Dir(outPath), 0755); err != nil {
			return err
		}

		fileInArchive, err := f.Open()
		if err != nil {
			return err
		}

		dstFile, err := os.Create(outPath)
		if err != nil {
			fileInArchive.Close()
			return err
		}

		buffer := make([]byte, MiB)
		for {
			n, readErr := fileInArchive.Read(buffer)
			if n > 0 {
				_, writeErr := dstFile.Write(buffer[:n])
				if writeErr != nil {
					dstFile.Close()
					fileInArchive.Close()
					return writeErr
				}

				done += int64(n)
				printProgress(done, totalSize, startTime, "Extracting")
			}

			if readErr != nil {
				if readErr == io.EOF {
					break
				}
				dstFile.Close()
				fileInArchive.Close()
				return readErr
			}
		}

		dstFile.Close()
		fileInArchive.Close()
		fmt.Printf("\rExtracted %d/%d files", i+1, len(reader.File))
	}

	fmt.Println("\nExtraction complete")
	return nil
}

func readPassword() (string, error) {
	fmt.Print("Enter password: ")
	passwordBytes, err := term.ReadPassword(int(os.Stdin.Fd()))
	fmt.Println()
	if err != nil {
		return "", err
	}
	return string(passwordBytes), nil
}

func parseCommandLine() (*bool, *string, *string, *string, error) {
	if len(os.Args) < 3 {
		return nil, nil, nil, nil, errors.New("Usage: base.go -encrypt/-decrypt filename")
	}

	var encrypt bool
	if os.Args[1] == "-encrypt" {
		encrypt = true
	} else if os.Args[1] == "-decrypt" {
		encrypt = false
	} else {
		return nil, nil, nil, nil, errors.New("Must specify -encrypt or -decrypt")
	}

	input := os.Args[2]
	var comments string

	return &encrypt, &input, nil, &comments, nil
}

func main() {
	var encryptCmd *bool
	var inputFlag *string
	var outputFlag *string
	var commentsFlag *string
	var err error

	if len(os.Args) > 1 && (os.Args[1] == "-encrypt" || os.Args[1] == "-decrypt") {
		encryptCmd, inputFlag, outputFlag, commentsFlag, err = parseCommandLine()
		if err != nil {
			fmt.Println(err)
			return
		}

		if commentsFlag != nil {
			comments = *commentsFlag
		}
	} else {
		encryptCmd = flag.Bool("encrypt", false, "Encrypt file mode")
		decryptCmd := flag.Bool("decrypt", false, "Decrypt file mode")
		passwordStr := flag.String("password", "", "Password for encryption/decryption")
		inputFlag = flag.String("input", "", "Input file path")
		outputFlag = flag.String("output", "", "Output file path")
		keyfilesStr := flag.String("keyfiles", "", "Comma-separated list of keyfile paths")
		commentsFlag = flag.String("comments", "", "Comments to add (encryption only)")
		configPath := flag.String("config", "", "Path to config file")
		generatePassword := flag.Bool("genpass", false, "Generate a secure random password")
		passwordLength := flag.Int("passlength", 32, "Length of generated password")

		flag.Parse()

		if *generatePassword {
			password := genPassword(*passwordLength)
			fmt.Println("Generated password:", password)
			return
		}

		if *decryptCmd {
			tmp := false
			encryptCmd = &tmp
		}

		if *passwordStr != "" {
			password = *passwordStr
		}

		if *keyfilesStr != "" {
			keyfiles = strings.Split(*keyfilesStr, ",")
		}

		if *configPath != "" {
			loadConfig(*configPath)
		}

		if *commentsFlag != "" {
			comments = *commentsFlag
		}
	}

	if *inputFlag == "" {
		fmt.Println("Error: Must specify input file")
		fmt.Println("---------------------------------------")
		fmt.Println("Example usage:")
		fmt.Println("go run base.go -encrypt input.txt")
		fmt.Println("go run base.go -decrypt input.txt.kyi")
		fmt.Println("---------------------------------------")
		return
	}

	if _, err := os.Stat(*inputFlag); os.IsNotExist(err) {
		fmt.Printf("Error: Input file %s does not exist\n", *inputFlag)
		return
	}

	if *encryptCmd {
		mode = "encrypt"
	} else {
		mode = "decrypt"
	}

	inputFile = *inputFlag

	if outputFlag == nil || *outputFlag == "" {
		if mode == "encrypt" {
			outputFile = inputFile + ".kyi"
		} else {
			if strings.HasSuffix(inputFile, ".kyi") {
				outputFile = strings.TrimSuffix(inputFile, ".kyi")
			} else {
				outputFile = inputFile + ".decrypted"
			}
		}
	} else {
		outputFile = *outputFlag
	}

	if password == "" {
		if mode == "decrypt" {
			fin, err := os.Open(inputFile)
			if err == nil {
				defer fin.Close()

				versionBytes := make([]byte, 15)
				fin.Read(versionBytes)

				commentLengthBytes := make([]byte, 15)
				fin.Read(commentLengthBytes)
				commentLengthBytes, err = rsDecode(rs5, commentLengthBytes)

				if err == nil {
					if valid, _ := regexp.Match(`^\d{5}$`, commentLengthBytes); valid {
						commentsLength, _ := strconv.Atoi(string(commentLengthBytes))

						if commentsLength > 0 {
							commentBytes := make([]byte, commentsLength*3)
							fin.Read(commentBytes)

							extractedComment := ""
							for i := 0; i < commentsLength*3; i += 3 {
								t, err := rsDecode(rs1, commentBytes[i:i+3])
								if err != nil {
									extractedComment = "Comments are corrupted"
									break
								}
								extractedComment += string(t)
							}

							if extractedComment != "" && extractedComment != "Comments are corrupted" {
								fmt.Printf("Comment (read): %s\n", extractedComment)
							}
						}
					}
				}
			}
		}

		fmt.Print("Enter password: ")
		passwordBytes, err := term.ReadPassword(int(os.Stdin.Fd()))
		fmt.Println()
		if err != nil {
			fmt.Printf("Error reading password: %v\n", err)
			return
		}
		password = string(passwordBytes)
	}

	if mode == "encrypt" && comments == "" {
		if password != "" && comments == "" {
			fmt.Print("Confirm password: ")
			confirmBytes, err := term.ReadPassword(int(os.Stdin.Fd()))
			fmt.Println()
			if err != nil {
				fmt.Printf("Error reading password: %v\n", err)
				return
			}

			if string(confirmBytes) != password {
				fmt.Println("Error: Passwords do not match")
				return
			}
		}

		fmt.Print("Comment (optional): ")
		var commentBytes []byte
		commentBytes, err = bufio.NewReader(os.Stdin).ReadBytes('\n')
		if err != nil && err != io.EOF {
			fmt.Printf("Error reading comment: %v\n", err)
			return
		}
		comments = string(commentBytes[:len(commentBytes)-1])
	} else if mode == "decrypt" {
		fin, err := os.Open(inputFile)
		if err == nil {
			defer fin.Close()

			versionBytes := make([]byte, 15)
			fin.Read(versionBytes)

			commentLengthBytes := make([]byte, 15)
			fin.Read(commentLengthBytes)
			commentLengthBytes, err = rsDecode(rs5, commentLengthBytes)

			if err == nil {
				if valid, _ := regexp.Match(`^\d{5}$`, commentLengthBytes); valid {
					commentsLength, _ := strconv.Atoi(string(commentLengthBytes))

					if commentsLength > 0 {
						commentBytes := make([]byte, commentsLength*3)
						fin.Read(commentBytes)

						extractedComment := ""
						for i := 0; i < commentsLength*3; i += 3 {
							t, err := rsDecode(rs1, commentBytes[i:i+3])
							if err != nil {
								extractedComment = "Comments are corrupted"
								break
							}
							extractedComment += string(t)
						}

						if extractedComment != "" && extractedComment != "Comments are corrupted" {
							fmt.Printf("Comment (read): %s\n", extractedComment)
						}
					}
				}
			}
		}
	}

	config = defaultConfig

	if mode == "encrypt" {
		err = work(true)
	} else {
		err = work(false)
	}

	if err != nil {
		fmt.Printf("Error: %v\n", err)
	}
}
