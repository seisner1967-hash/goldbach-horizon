"""Compile only this role's new module, after the root-inspected numeric PASS."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from datetime import datetime, timezone

sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
R = W.parents[1]
LEAN = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE = Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']
ROOT_OBSERVATION = R / '.arbor' / 'sessions' / 'parity' / '.coordinator' / 'messages' / 'round18_typeii_root_observation.json'
NUMERIC_RECEIPT = R / 'round18' / 'role6' / 'typeii_canonical_receipt.json'
NUMERIC_OUTPUT = R / 'round18' / 'typeii.json'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def write_json(path, obj):
    Path(path).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')

observation = json.loads(ROOT_OBSERVATION.read_text(encoding='utf-8'))
numeric = json.loads(NUMERIC_RECEIPT.read_text(encoding='utf-8'))
assert observation['formal3_candidate_compilation_authorized'] is True
assert observation['actual_exit_code'] == 0 and observation['actual_identity_false'] is False
assert numeric['canonical_pass'] is True and numeric['exit_code'] == 0
assert sha(NUMERIC_OUTPUT) == numeric['output_sha256'] == observation['checked_inputs_sha256']['typeii.json']
assert sha(NUMERIC_RECEIPT) == observation['checked_inputs_sha256']['role6/typeii_canonical_receipt.json']

source = W / (sys.argv[1] if len(sys.argv) > 1 else 'SeparatedTypeIICount.lean')
assert source.resolve().parent == W.resolve() and source.suffix == '.lean'
code = source.read_text(encoding='utf-8').split('-- AXIOM_AUDIT_BEGIN')[0].rstrip() + '\n'
assert not re.search(r'\b(?:sorry|admit|axiom|native_decide|trustMe)\b', code)
decls = re.findall(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|structure)\s+([A-Za-z][A-Za-z0-9_\']*)', code, re.M)
prefix = 'GoldbachRound18.SeparatedTypeII.'
audit = '\n-- AXIOM_AUDIT_BEGIN\n' + '\n'.join('#print axioms ' + prefix + name for name in decls) + '\n'
source.write_text(code + audit, encoding='utf-8')

receipt_path = W / 'crt_build_receipt.json'
record = json.loads(receipt_path.read_text(encoding='utf-8')) if receipt_path.exists() else {
    'attempts': [], 'old_Lean_rebuilds': 0, 'old_producers_replayed': 0,
    'old_oleans_copied': 0, 'victory': False,
}
n = len(record['attempts']) + 1
snapshot = W / f'crt_attempt{n:02d}_{source.stem}_source.lean.txt'
assert not snapshot.exists(), 'Capture already exists'
snapshot.write_bytes(source.read_bytes())
builder_snapshot = W / f'crt_attempt{n:02d}_builder.py.txt'
assert not builder_snapshot.exists(), 'Builder capture already exists'
builder_snapshot.write_bytes(Path(__file__).read_bytes())
olean = W / (source.stem + '.olean')
command = [str(LEAN), '-o', str(olean), str(source)]
env = dict(os.environ)
env['LEAN_PATH'] = ';'.join(map(str, [W, *[CACHE / p / '.lake' / 'build' / 'lib' for p in PACKAGES]]))
started = {
    'attempt': n, 'state': 'STARTED', 'started_at_utc': datetime.now(timezone.utc).isoformat(),
    'source': str(source), 'source_sha256': sha(source), 'source_snapshot': str(snapshot),
    'snapshot_sha256': sha(snapshot), 'builder_snapshot': str(builder_snapshot),
    'builder_sha256': sha(builder_snapshot), 'command': command, 'cwd': str(W),
    'LEAN_PATH': env['LEAN_PATH'], 'lean_exe_sha256': sha(LEAN),
    'root_observation_sha256': sha(ROOT_OBSERVATION), 'numeric_receipt_sha256': sha(NUMERIC_RECEIPT),
    'numeric_output_sha256': sha(NUMERIC_OUTPUT), 'new_declarations': decls,
    'old_Lean_rebuilds': 0, 'old_producers_replayed': 0, 'old_oleans_copied': 0,
}
write_json(W / f'crt_attempt{n:02d}_started.json', started)
proc = subprocess.run(command, cwd=W, env=env, capture_output=True)
log = W / f'crt_attempt{n:02d}.log'
log.write_bytes(proc.stdout + proc.stderr)
assert source.read_bytes() == snapshot.read_bytes(), 'Concurrent source mutation'
row = dict(started, state='FINISHED', finished_at_utc=datetime.now(timezone.utc).isoformat(),
           exit_code=proc.returncode, log=str(log), log_sha256=sha(log))
if proc.returncode == 0:
    preserved = W / f'crt_attempt{n:02d}_fresh_pass.olean'
    preserved.write_bytes(olean.read_bytes())
    row.update(olean=str(olean), olean_sha256=sha(olean),
               preserved_olean=str(preserved), preserved_olean_sha256=sha(preserved))
record['attempts'].append(row)
write_json(W / f'crt_attempt{n:02d}_receipt.json', row)
write_json(receipt_path, record)
print(json.dumps({'attempt': n, 'exit_code': proc.returncode, 'source_sha256': sha(source), 'log_sha256': sha(log)}))
print(log.read_text(encoding='utf-8', errors='replace'))
sys.exit(proc.returncode)
