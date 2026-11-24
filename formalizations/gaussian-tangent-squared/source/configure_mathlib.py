#!/usr/bin/env python3
"""Select an installed, cached, pinned Mathlib bundle without downloading anything."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

PIN = '9944fe2973b8dc0b86949101ed98232c07cd54a0'
ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument('--mathlib', type=Path)
args = parser.parse_args()
candidates = [args.mathlib, Path(os.environ['TANGENT_SQUARED_MATHLIB']) if os.environ.get('TANGENT_SQUARED_MATHLIB') else None, Path('/opt/mathlib4')]
bundle = next((p.resolve() for p in candidates if p and (p/'Mathlib').is_dir() and (p/'lean-toolchain').is_file()), None)
if bundle is None:
    raise SystemExit('No installed Mathlib found; pass --mathlib /absolute/path/to/the/pinned/bundle.')
if (bundle/'lean-toolchain').read_text().strip() != (ROOT/'lean-toolchain').read_text().strip():
    raise SystemExit('The installed Mathlib toolchain differs from the project toolchain.')
if (bundle/'.git').exists():
    revision = subprocess.check_output(['git', '-C', str(bundle), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != PIN:
        raise SystemExit('Mathlib revision mismatch: '+revision)
else:
    print('Bundle has no Git metadata; confirm externally that its revision is '+PIN)
packages = bundle/'.lake/packages'
if not packages.is_dir():
    raise SystemExit('The installed bundle has no cached .lake/packages directory.')
configuration = ROOT/'lakefile.toml'
s = configuration.read_text()
s, n = re.subn(r'(\[\[require\]\]\s*name\s*=\s*"mathlib"\s*path\s*=\s*)"[^"]*"', lambda m: m.group(1)+json.dumps(str(bundle)), s)
if n != 1:
    raise SystemExit('Expected exactly one Mathlib path dependency.')
configuration.write_text(s)
manifest = ROOT/'lake-manifest.json'
m = json.loads(manifest.read_text())
for package in m['packages']:
    if package['name'] == 'mathlib':
        package['dir'] = str(bundle)
manifest.write_text(json.dumps(m, indent=2)+'\n')
local = ROOT/'.lake/packages'
local.parent.mkdir(exist_ok=True)
if local.is_symlink():
    if local.resolve() != packages.resolve():
        raise SystemExit('Existing dependency symlink points to another bundle.')
elif local.exists():
    raise SystemExit('Existing .lake/packages is not a symlink; inspect it before configuring.')
else:
    local.symlink_to(packages, target_is_directory=True)
print('Configured Mathlib:', bundle)
print('Pinned revision:', PIN)
print('Toolchain:', (ROOT/'lean-toolchain').read_text().strip())
print('Dependency cache:', packages)
