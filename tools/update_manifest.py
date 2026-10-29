"""Explicitly rebuild the publication checksum manifest after reviewed changes."""
from pathlib import Path
import hashlib
import json
import os

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "verification/files.sha256.json"
IGNORE = {".git", ".venv", "venv", "build", "__pycache__", ".pytest_cache", ".ruff_cache"}
files = {}
for directory, children, names in os.walk(ROOT):
    children[:] = sorted(child for child in children if child not in IGNORE)
    for name in sorted(names):
        path = Path(directory) / name
        if path == TARGET or path.suffix in {".pyc", ".pyo"}:
            continue
        if name == ".env" or name.startswith(".env."):
            raise SystemExit("Refusing to include an environment file.")
        files[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
TARGET.write_text(json.dumps({"algorithm": "SHA-256", "files": dict(sorted(files.items()))}, indent=2) + "\n", encoding="utf-8", newline="\n")
print(f"Recorded {len(files)} publication files.")
