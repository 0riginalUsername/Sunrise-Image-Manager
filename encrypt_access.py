#!/usr/bin/env python3
"""
Quick utility script to encrypt access.json credentials using keyring.
Run this once to migrate from plain-text to encrypted storage.
"""

import sys
from pathlib import Path

# Add the current directory to path so we can import SIM_configured
sys.path.insert(0, str(Path(__file__).parent))

from SIM_configured import encrypt_existing_access_json, ACCESS_JSON_PATH

if __name__ == "__main__":
    print(f"Encrypting access.json at: {ACCESS_JSON_PATH}")
    print("This will move AWS credentials to your system keyring...")
    
    if encrypt_existing_access_json():
        print("[SUCCESS] access.json has been encrypted.")
        print("   Credentials are now stored securely in keyring.")
        print("   The access.json file now only contains metadata.")
    else:
        print("[ERROR] Failed to encrypt access.json. Check the logs above for details.")
        sys.exit(1)
