"""Offline role3 builder: checks the new finite gate, compiles only the new module."""
import sys
sys.dont_write_bytecode = True
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
from pathlib import Path
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
COMPILER = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE = Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']
SOURCE = ROOT / 'lean' / 'SquarefreeLcmCoefficient.lean'
BUILD = ROOT / 'role3_build'
BUILD.mkdir(exist_ok=True)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

gate_path = ROOT / 'ap_prefix.json'
gate = json.loads(gate_path.read_text(encoding='utf-8'))
assert gate['N'] == 100000000
assert gate['status'] == 'PASS_NEW_FINITE_CONTRACTS_ONLY'
assert gate['finite_coefficients']['B6_guarded_finite_product']['status'] == 'PASS_IDENTITY_ONLY'
assert gate['script_sha256'] == sha(ROOT / 'ap_prefix_checks.py')
assert not gate['victory']
assert sha(ROOT / 'agent2_bilateral_compensation.md') == 'ea3d4944f5a55df6eb9bbc30fed1fb90a00d24b2c505d196d8b61559394e9830'
paths = [CACHE / name / '.lake' / 'build' / 'lib' for name in PACKAGES]
assert all(path.is_dir() for path in paths)
assert COMPILER.is_file()
version = subprocess.run([str(COMPILER), '--version'], capture_output=True, text=True, encoding='utf-8', errors='replace')
assert version.returncode == 0 and 'version 4.15.0' in version.stdout
env = dict(os.environ)
env['LEAN_PATH'] = ';'.join(str(path) for path in paths)
receipt_path = ROOT / 'role3_build_receipt.json'
receipt = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else {'attempts': []}
attempt = len(receipt['attempts']) + 1
stem = f'attempt{attempt:02d}'
source_snapshot = BUILD / f'{stem}_source.txt'
source_snapshot.write_bytes(SOURCE.read_bytes())
olean = BUILD / 'SquarefreeLcmCoefficient.olean'
command = [str(COMPILER), '-o', str(olean), str(SOURCE)]
completed = subprocess.run(command, cwd=SOURCE.parent, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
log = BUILD / f'{stem}.log'
output = completed.stdout + completed.stderr
log.write_text(output, encoding='utf-8')
entry = {
    'attempt': attempt, 'timestamp_utc': datetime.now(timezone.utc).isoformat(),
    'command_argv': command, 'cwd': str(SOURCE.parent),
    'source_sha256': sha(SOURCE), 'source_snapshot': str(source_snapshot),
    'exit_code': completed.returncode, 'log': str(log), 'log_sha256': sha(log),
    'gate_sha256': sha(gate_path), 'gate_script_sha256': sha(ROOT / 'ap_prefix_checks.py'),
    'gate_status': gate['finite_coefficients']['B6_guarded_finite_product']['status'], 'gate_N': gate['N'],
}
receipt['attempts'].append(entry)
receipt.update({
    'compiler': str(COMPILER), 'compiler_version': version.stdout.strip(),
    'lean_path': env['LEAN_PATH'], 'source': str(SOURCE), 'source_sha256': sha(SOURCE),
    'status': 'COMPILED_AUXILIARY_IDENTITY' if completed.returncode == 0 else 'COMPILER_ERROR',
    'only_new_module_compiled': True, 'old_bank_replayed': False,
    'victory': False, 'unresolved': ['B13 bilateral signed compensation', 'source physical-band BV onset', 'covered bridge e'],
})
if completed.returncode == 0:
    receipt['olean'] = str(olean)
    receipt['olean_sha256'] = sha(olean)
    receipt['axiom_output'] = output
receipt_path.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps({'attempt': attempt, 'exit_code': completed.returncode, 'gate_sha256': sha(gate_path), 'receipt': str(receipt_path)}, ensure_ascii=False))
print(output)
sys.exit(completed.returncode)
