#!/usr/bin/env python3
"""
rebuild_rosetta_friend_audit_pack_zip.py
Rebuilds the ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK.zip archive from the updated directory.

Author: Qamar Munawer, Brandenburg University of Technology Cottbus-Senftenberg
Methodology note: ai is being used as a tool.
Epistemic invariant: all four Clay Millennium Problems remain strictly OPEN (status: verified-finite).
"""

import os
import zipfile
from pathlib import Path

def main():
    pack_dir = Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK")
    zip_path = Path("d:/Comfy UI/ROSETTA_4WORKSPACE_FRIEND_AUDIT_PACK.zip")

    print(f"[*] Packaging {pack_dir} into {zip_path}...")
    file_count = 0
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
        for root, dirs, files in os.walk(pack_dir):
            # Exclude pycache and temporary files
            dirs[:] = [d for d in dirs if d != "__pycache__" and not d.startswith(".")]
            for file in files:
                if file.endswith(".pyc") or file.endswith(".tmp"):
                    continue
                file_path = Path(root) / file
                rel_path = file_path.relative_to(pack_dir)
                zf.write(file_path, arcname=str(rel_path))
                file_count += 1

    zip_size = zip_path.stat().st_size
    print(f"[+] Successfully rebuilt {zip_path}: {file_count} files, {zip_size:,} bytes")

if __name__ == "__main__":
    main()
