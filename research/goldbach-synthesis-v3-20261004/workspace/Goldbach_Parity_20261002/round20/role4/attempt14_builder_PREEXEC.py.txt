"""Compile a fresh role4 module only after the distinct ROOT20 gate.
Historical sources are hash-checked imports, never compiler targets.
"""
import sys, os, json, hashlib, subprocess, re
from pathlib import Path
from datetime import datetime, timezone
sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
B = W.parents[1]
LEAN = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE = Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib',
            'plausible', 'proofwidgets', 'Qq']
MODULES = ['FriablePhysicalPrefix.lean', 'FriableEulerRankin.lean',
           'FriablePrimeHarmonic.lean', 'FriableTotientEnvelope.lean',
           'FriableKernelEnvelope.lean', 'FriablePhysicalPayment.lean']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def now(): return datetime.now(timezone.utc).isoformat()
def save_new(p, data):
    with p.open('x', encoding='utf-8') as h:
        h.write(json.dumps(data, indent=2, ensure_ascii=False)+'\n')
if len(sys.argv) != 3:
    raise SystemExit('Require a new module filename and explicit root gate path')
src = (W / sys.argv[1]).resolve()
assert src.parent == W and src.name in MODULES
gate_path = Path(sys.argv[2]).resolve()
assert gate_path.exists(), 'NO LEAN: explicit ROOT20 authorization absent'
gate = json.loads(gate_path.read_text(encoding='utf-8'))
assert gate['authorization'] == 'ROOT20_FORMAL4_COMPILE'
assert gate['root_authorized'] is True
assert gate['canonical_new_numeric_pass_inspected'] is True
assert gate['round'] == 20 and gate['node'] == '14.5'
assert gate['builder_sha256'] == sha(Path(__file__))
numeric_bindings = gate['numeric_bindings']
assert numeric_bindings
for rel, expected in numeric_bindings.items():
    p = (B / rel).resolve()
    assert p.is_relative_to(B) and rel.startswith('round20/')
    assert sha(p) == expected, 'new numerical gate binding changed'
numeric_receipt = B / gate['numeric_receipt_relative_path']
assert gate['numeric_receipt_relative_path'] in numeric_bindings
actual = json.loads(numeric_receipt.read_text(encoding='utf-8'))
assert actual['exit_code'] == 0, 'actual new canonical subprocess did not pass'
deps_path = W / 'dependencies_readonly.json'
deps = json.loads(deps_path.read_text(encoding='utf-8'))['bindings']
for rel, expected in deps.items():
    assert sha(B / rel) == expected, 'historical read-only dependency changed'
assert sha(LEAN) == '8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
content = src.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|native_decide|trustMe)\b', content)
assert not re.search(r'^\s*axiom\s+', content, re.M)
ledger_path = W / 'build_receipt.json'
record = json.loads(ledger_path.read_text(encoding='utf-8')) if ledger_path.exists() else {
    'round': 20, 'role': 4, 'attempts': [], 'historical_source_compiles': 0,
    'successful_modules': {}, 'score': 0, 'victory': False}
assert src.name not in record['successful_modules'], 'unchanged PASS replay prohibited'
new_import_bindings = {}
for module in record['successful_modules'].values():
    for k in ['source', 'olean']:
        p = Path(module[k])
        assert sha(p) == module[k+'_sha256'], 'frozen new import changed'
        new_import_bindings[str(p)] = module[k+'_sha256']
n = len(record['attempts']) + 1
snapshot = W / f'attempt{n:02d}_source_PREEXEC.lean.txt'
builder = W / f'attempt{n:02d}_builder_PREEXEC.py.txt'
with snapshot.open('xb') as h: h.write(src.read_bytes())
with builder.open('xb') as h: h.write(Path(__file__).read_bytes())
started = W / f'attempt{n:02d}_started.json'
log = W / f'attempt{n:02d}.log'
out = W / f'attempt{n:02d}.olean'
env = dict(os.environ)
env['LEAN_PATH'] = ';'.join(map(str, [W, B/'round19'/'judge'/'build',
    B/'round18'/'judge'/'build', B/'round16'/'judge'/'build',
    B/'round13'/'role4'/'dependencies',
    *[CACHE/p/'.lake'/'build'/'lib' for p in PACKAGES]]))
env['PYTHONDONTWRITEBYTECODE'] = '1'
cmd = [str(LEAN), '-o', str(out), str(src)]
entry = {'attempt': n, 'phase': 'PREEXEC', 'started_utc': now(),
    'source': str(src), 'source_sha256': sha(src),
    'snapshot': str(snapshot), 'snapshot_sha256': sha(snapshot),
    'builder_snapshot': str(builder), 'builder_snapshot_sha256': sha(builder),
    'command': cmd, 'cwd': str(W), 'LEAN_PATH': env['LEAN_PATH'],
    'compile_gate': str(gate_path), 'compile_gate_sha256': sha(gate_path),
    'numeric_bindings': numeric_bindings, 'dependency_bindings': deps,
    'new_import_bindings': new_import_bindings,
    'dependencies_manifest_sha256': sha(deps_path), 'compiler_sha256': sha(LEAN)}
save_new(started, entry)
run = subprocess.run(cmd, cwd=W, env=env, capture_output=True, text=True,
                     encoding='utf-8', errors='replace')
with (W / f'attempt{n:02d}.stdout.txt').open('x', encoding='utf-8') as h: h.write(run.stdout)
with (W / f'attempt{n:02d}.stderr.txt').open('x', encoding='utf-8') as h: h.write(run.stderr)
with log.open('x', encoding='utf-8') as h: h.write(run.stdout+run.stderr)
assert src.read_bytes() == snapshot.read_bytes(), 'source mutated during compiler invocation'
entry.update({'phase': 'FINISHED', 'finished_utc': now(), 'exit_code': run.returncode,
    'started_receipt': str(started), 'started_receipt_sha256': sha(started),
    'stdout': run.stdout, 'stderr': run.stderr,
    'log': str(log), 'log_sha256': sha(log),
    'olean': str(out) if out.exists() else None,
    'olean_sha256': sha(out) if out.exists() else None})
record['attempts'].append(entry)
if run.returncode == 0:
    assert 'sorryAx' not in run.stdout+run.stderr
    final = src.with_suffix('.olean')
    with final.open('xb') as h: h.write(out.read_bytes())
    record['successful_modules'][src.name] = {'attempt': n,
        'source': str(src), 'source_sha256': sha(src),
        'olean': str(final), 'olean_sha256': sha(final)}
ledger_path.write_text(json.dumps(record, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
print(json.dumps({'attempt': n, 'module': src.name, 'exit_code': run.returncode,
                  'source_snapshot': str(snapshot), 'log': str(log)}))
print(run.stdout+run.stderr)
sys.exit(run.returncode)
