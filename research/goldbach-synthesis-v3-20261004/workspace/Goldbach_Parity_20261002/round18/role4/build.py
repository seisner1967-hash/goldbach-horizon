"""Compile only new role4/18 sources after the explicit root/numeric gate.
Every invocation gets a PREEXEC snapshot and started receipt before Lean.
No lake build, import-source rebuilding, or historical bank is invoked.
"""
import sys, os, json, hashlib, subprocess
from pathlib import Path
from datetime import datetime, timezone
sys.dont_write_bytecode = True
W = Path(__file__).resolve().parent
R = W.parents[1]
LEAN = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE = Path(r'D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages')
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib',
            'plausible', 'proofwidgets', 'Qq']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def now(): return datetime.now(timezone.utc).isoformat()
gate_path = Path(sys.argv[2]).resolve() if len(sys.argv) > 2 else W / 'compile_gate.json'
if not gate_path.exists():
    raise SystemExit('NO LEAN: canonical SS PASS / root authorization gate is absent')
gate = json.loads(gate_path.read_text(encoding='utf-8'))
assert gate['root_authorized'] is True and gate['canonical_SS_PASS_inspected'] is True
numeric_bindings = gate['numeric_bindings']
for rel in ['round18/semiprime.json', 'round18/role6/semiprime_canonical_receipt.json']:
    assert sha(R / rel) == numeric_bindings[rel], 'numeric gate binding changed'
canonical = json.loads((R/'round18'/'role6'/'semiprime_canonical_receipt.json').read_text(encoding='utf-8'))
assert canonical['exit_code'] == 0 and canonical['canonical_pass'] is True
assert canonical['output_sha256'] == sha(R/'round18'/'semiprime.json')
dependency_path = W / 'dependencies_readonly.json'
dependency_bindings = json.loads(dependency_path.read_text(encoding='utf-8'))['bindings']
for rel, expected in dependency_bindings.items():
    assert sha(R / rel) == expected, 'read-only historical dependency changed'
src = (W / sys.argv[1]).resolve()
assert src.parent == W and src.suffix == '.lean'
assert not any(token in src.read_text(encoding='utf-8') for token in
               ['sorry', 'admit', 'native_decide', 'trustMe'])
ledger_path = W / 'build_receipt.json'
record = json.loads(ledger_path.read_text(encoding='utf-8')) if ledger_path.exists() else {
    'attempts': [], 'historical_source_compiles': 0, 'score': 0, 'victory': False}
assert src.name not in record.get('successful_modules', {}), 'a PASS module must not be recompiled'
new_import_bindings = {}
for mod in record.get('successful_modules', {}).values():
    for key in ['source', 'olean']:
        p = Path(mod[key])
        assert sha(p) == mod[key+'_sha256'], 'a frozen new import changed'
        new_import_bindings[str(p)] = mod[key+'_sha256']
n = len(record['attempts']) + 1
snap = W / f'attempt{n:02d}_source.lean.txt'
with snap.open('xb') as handle:
    handle.write(src.read_bytes())
builder_snap = W / f'attempt{n:02d}_builder.py.txt'
with builder_snap.open('xb') as handle:
    handle.write(Path(__file__).read_bytes())
out = W / f'attempt{n:02d}.olean'
log = W / f'attempt{n:02d}.log'
started = W / f'attempt{n:02d}_started.json'
env = dict(os.environ)
paths = [W, R/'round17'/'role4', R/'round17'/'role3',
         R/'round16'/'role3', R/'round16'/'role4',
         R/'round13'/'role4'/'dependencies',
         *[CACHE/p/'.lake'/'build'/'lib' for p in PACKAGES]]
env['LEAN_PATH'] = ';'.join(map(str, paths))
cmd = [str(LEAN), '-o', str(out), str(src)]
entry = {'attempt': n, 'phase': 'PREEXEC', 'started_utc': now(),
         'source': str(src), 'source_sha256': sha(src),
         'snapshot': str(snap), 'snapshot_sha256': sha(snap),
         'builder_snapshot': str(builder_snap), 'builder_snapshot_sha256': sha(builder_snap),
         'command': cmd, 'cwd': str(W), 'LEAN_PATH': env['LEAN_PATH'],
         'compile_gate': str(gate_path), 'compile_gate_sha256': sha(gate_path),
         'numeric_bindings': numeric_bindings, 'dependency_bindings': dependency_bindings,
         'new_import_bindings': new_import_bindings,
         'dependencies_manifest_sha256': sha(dependency_path), 'compiler_sha256': sha(LEAN)}
with started.open('x', encoding='utf-8') as handle:
    handle.write(json.dumps(entry, indent=2, ensure_ascii=False)+'\n')
run = subprocess.run(cmd, cwd=W, env=env, capture_output=True,
                     text=True, encoding='utf-8', errors='replace')
with log.open('x', encoding='utf-8') as handle:
    handle.write(run.stdout+run.stderr)
assert src.read_bytes() == snap.read_bytes(), 'source changed during compilation'
entry.update(phase='FINISHED', finished_utc=now(), exit_code=run.returncode,
             started_receipt=str(started), started_receipt_sha256=sha(started),
             log=str(log), log_sha256=sha(log),
             olean=str(out) if out.exists() else None,
             olean_sha256=sha(out) if out.exists() else None)
record['attempts'].append(entry)
if run.returncode == 0:
    assert 'sorryAx' not in log.read_text(encoding='utf-8')
    final = src.with_suffix('.olean')
    final.write_bytes(out.read_bytes())
    record.setdefault('successful_modules', {})[src.name] = {
        'attempt': n, 'source': str(src), 'source_sha256': sha(src),
        'olean': str(final), 'olean_sha256': sha(final)}
ledger_path.write_text(json.dumps(record, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
print(json.dumps({'attempt': n, 'source': src.name, 'exit_code': run.returncode}))
print(run.stdout+run.stderr)
sys.exit(run.returncode)
