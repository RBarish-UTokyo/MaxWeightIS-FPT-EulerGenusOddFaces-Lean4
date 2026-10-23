#!/usr/bin/env bash
# Local verification of the exact source snapshot. Official Palomar
# verification is a separate isolated run of the registry workflow.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_sources.py > /dev/null
python3 scripts/generate_challenge.py --check
lake exe cache get
lake build AllModules MWIS Challenge Solution Audit
lake env lean Audit.lean
prefix=$(lean --print-prefix)
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - "$prefix" "$config" <<'PY'
import json
import pathlib
import sys
prefix, destination = map(pathlib.Path, sys.argv[1:])
config = json.loads(pathlib.Path('comparator.json').read_text())
assert 'external_kernels' not in config
config['external_kernels'] = {
    'nanoda': [str(prefix / 'bin' / 'nanoda_bin')],
    'con-ron': [str(prefix / 'bin' / 'con-ron')],
}
destination.write_text(json.dumps(config, indent=2) + '\n')
PY
lake comparator --config "$config"
