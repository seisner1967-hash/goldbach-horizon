"""Offline U1 builder; preserves every candidate and compiler response."""
import sys
sys.dont_write_bytecode = True
sys.stdout.reconfigure(encoding='utf-8', errors='replace')
from pathlib import Path
import hashlib, json, os, subprocess
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
COMPILER = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE = Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']
SOURCE = ROOT / 'lean' / 'ShortDivisorComplement.lean'
BUILD = ROOT / 'role4_build'
BUILD.mkdir(exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
gate_path = ROOT / 'paired_cofactors.json'
gate = json.loads(gate_path.read_text(encoding='utf-8'))
assert gate['N'] == 100000000 and gate['status'] == 'PASS_FINITE_IDENTITIES_ONLY'
assert gate['dual_and_matched']['status'] == 'PASS_IDENTITY_ONLY'
assert gate['script_sha256'] == sha(ROOT / 'paired_cofactor_checks.py') == 'bdee7952e47419fef2a0512d8e74a7234bf3da6800e2dc9561b94f9bd34d5ef2'
assert sha(gate_path) == '909df1b5cd38a4ed42cad65ca8930c47930d7ba8afd356148d87f4c7edcf34b2'
assert not gate['victory']
assert sha(ROOT / 'agent1_prime_signed.md') == 'e439a43eea07380643c233ca6e48442d79e0c6cd1bdff4d67adc590797791064'
paths = [CACHE / name / '.lake' / 'build' / 'lib' for name in PACKAGES]
assert all(p.is_dir() for p in paths) and COMPILER.is_file()
version = subprocess.run([str(COMPILER), '--version'], capture_output=True, text=True, encoding='utf-8', errors='replace')
assert version.returncode == 0 and 'version 4.15.0' in version.stdout
env = dict(os.environ)
env['LEAN_PATH'] = ';'.join(str(p) for p in paths)
receipt_path = ROOT / 'role4_build_receipt.json'
receipt = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else {'attempts': []}
attempt = len(receipt['attempts']) + 1
stem = f'attempt{attempt:02d}'
snapshot = BUILD / f'{stem}_source.txt'
snapshot.write_bytes(SOURCE.read_bytes())
olean = BUILD / 'ShortDivisorComplement.olean'
command = [str(COMPILER), '-o', str(olean), str(SOURCE)]
completed = subprocess.run(command, cwd=SOURCE.parent, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
output = completed.stdout + completed.stderr
log = BUILD / f'{stem}.log'
log.write_text(output, encoding='utf-8')
receipt['attempts'].append({'attempt': attempt, 'timestamp_utc': datetime.now(timezone.utc).isoformat(),
 'command_argv': command, 'cwd': str(SOURCE.parent), 'source_sha256': sha(SOURCE),
 'source_snapshot': str(snapshot), 'exit_code': completed.returncode,
 'log': str(log), 'log_sha256': sha(log), 'gate_sha256': sha(gate_path),
 'gate_script_sha256': sha(ROOT / 'paired_cofactor_checks.py'), 'gate_status': gate['dual_and_matched']['status']})
receipt.update({'compiler': str(COMPILER), 'compiler_version': version.stdout.strip(),
 'lean_path': env['LEAN_PATH'], 'source': str(SOURCE), 'source_sha256': sha(SOURCE),
 'status': 'COMPILED_AUXILIARY_U1' if completed.returncode == 0 else 'COMPILER_ERROR',
 'only_new_module_compiled': True, 'old_bank_replayed': False, 'victory': False,
 'unresolved': ['signed H2-S*M2, J0 and incomplete J1 compensation', 'physical-band BV onset', 'covered 2*max(e,0)']})
if completed.returncode == 0:
 receipt.update({'olean': str(olean), 'olean_sha256': sha(olean), 'axiom_output': output})
receipt_path.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps({'attempt': attempt, 'exit_code': completed.returncode, 'source_sha256': sha(SOURCE), 'receipt': str(receipt_path)}, ensure_ascii=False))
print(output)
sys.exit(completed.returncode)
