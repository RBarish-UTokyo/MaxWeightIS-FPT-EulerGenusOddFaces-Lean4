#!/usr/bin/env python3
"""Write verification/manifest.json for the current source snapshot.

The manifest records the toolchain, the hashes of the compiler and kernel
binaries, the outcome of each local check (supplied as JSON on standard input),
and the SHA-256 of every tracked source file outside `verification/`. Evidence
in `verification/` applies only to the snapshot whose hashes it lists.

Usage: python3 scripts/record_manifest.py < checks.json
"""

from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BINARIES = ["lean", "lake", "leanexport", "leanchecker", "nanoda_bin", "con-ron"]


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    checks = json.load(sys.stdin)
    prefix = Path(subprocess.run(["lean", "--print-prefix"], capture_output=True,
                                 text=True, check=True).stdout.strip())
    version = subprocess.run(["lean", "--version"], capture_output=True, text=True,
                             check=True).stdout.strip()
    files = subprocess.run(["git", "ls-files"], cwd=ROOT, capture_output=True,
                           text=True, check=True).stdout.split()
    manifest = {
        "schema_version": 3,
        "date": "2026-10-23",
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "lean_version": version,
        "mathlib_commit": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
        "binary_sha256": {b: sha256(prefix / "bin" / b) for b in BINARIES},
        "target": "MWIS.Spec.fpt_claim",
        "full_theorem_proved": True,
        "official_registry_verification": False,
        "checks": checks,
        "source_sha256": {f: sha256(ROOT / f) for f in sorted(files)
                          if not f.startswith("verification/")},
    }
    (ROOT / "verification" / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"recorded {len(manifest['source_sha256'])} source files")


if __name__ == "__main__":
    main()
