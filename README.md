# KeyIn 🔐

**KeyIn** is a lightweight and secure command-line tool for file encryption and decryption.  
Built on the foundation of [Picocrypt](https://github.com/Picocrypt/Picocrypt?tab=readme-ov-file), it provides a simple yet robust solution for protecting your data.

KeyIn supports a wide range of file formats, including `.mp4`, `.jpg`, `.docx`, `.mp3`, `.pdf`, and more.

## Features

- 🔐 Strong encryption for sensitive files  
- 📁 Compatible with virtually all file types  
- ⚙️ Minimalistic and easy to use  
- 🚫 No external dependencies required  

## Usage

```bash
# Encrypt a file
go run base.go -encrypt <path-to-file>

# Decrypt a file
go run base.go -decrypt <path-to-file>.kyi
