#!/usr/bin/env python3
"""Check local source hygiene and the Palomar source-size requirements."""
from pathlib import Path
import json
import re
import sys

root = Path(__file__).resolve().parents[1]

def without_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            j = text.find('\n', i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated block comment')
    return ''.join(out)

errors, inventory = [], []
for path in sorted(root.rglob('*.lean')):
    rel = path.relative_to(root)
    if any(p in {'.lake', '.git'} for p in rel.parts):
        continue
    if path.is_symlink():
        errors.append(f'{rel}: symbolic link')
        continue
    raw = path.read_text(encoding='utf-8')
    clean = without_comments(raw)
    lines = len(raw.splitlines())
    if path.name != 'lakefile.lean' and not re.match(r'\s*module\b', clean):
        errors.append(f'{rel}: missing module header')
    if lines > 10000:
        errors.append(f'{rel}: exceeds 10000 lines')
    if rel.as_posix() == 'Challenge.lean':
        if lines > 1000 or len(raw.encode()) > 100 * 1024:
            errors.append('Challenge.lean: exceeds hard audit-surface limit')
        if re.search(r'^\s*(?:public\s+)?import\s+(?!Mathlib(?:\.|\s|$)|Init(?:\.|\s|$)|Std(?:\.|\s|$))', clean, re.M):
            errors.append('Challenge.lean: nonstandard direct import')
    elif re.search(r'\b(sorry|admit|axiom|native_decide)\b|Lean\.ofReduceBool', clean):
        errors.append(f'{rel}: forbidden proof placeholder or axiom mechanism')
    inventory.append({'path': rel.as_posix(), 'lines': lines,
                      'bytes': len(raw.encode())})

# Registry repository rules: no compiled artifacts outside .lake, no symlinked
# sources, no submodules, exactly one conventional licence file, size limit.
bad_suffixes = {'.olean', '.ilean', '.a', '.bc', '.dll', '.dylib', '.o', '.obj', '.so', '.trace'}
total = 0
for path in root.rglob('*'):
    rel = path.relative_to(root)
    if any(p in {'.lake', '.git'} for p in rel.parts):
        continue
    if path.is_file() and not path.is_symlink():
        total += path.stat().st_size
        if path.suffix in bad_suffixes:
            errors.append(f'{rel}: compiled artifact outside .lake')
if total > 500 * 1024 * 1024:
    errors.append('repository exceeds 500 MiB')
if (root / '.gitmodules').exists():
    errors.append('git submodules are not permitted')
licences = [p.name for p in root.iterdir() if re.fullmatch(
    r'(LICEN[CS]E|COPYING|UNLICENSE|OFL)(\.(md|markdown|txt))?', p.name, re.I)]
if len(licences) != 1:
    errors.append(f'expected exactly one licence file at the root, found {licences}')

config = json.loads((root / 'comparator.json').read_text())
allowed = {'challenge_module', 'solution_module', 'theorem_names',
           'definition_names', 'permitted_axioms', 'enable_nanoda'}
if set(config) - allowed:
    errors.append('Comparator configuration has unsupported fields')
if set(config.get('permitted_axioms', [])) - {'propext', 'Quot.sound', 'Classical.choice'}:
    errors.append('Comparator permits a nonstandard axiom')
if not config.get('theorem_names'):
    errors.append('Comparator theorem list is empty')

print(json.dumps({'date': '2026-10-23', 'sources': inventory,
                  'errors': errors}, indent=2))
sys.exit(bool(errors))
