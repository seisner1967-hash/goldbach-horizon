"""New all-rank aggregation only; imports seven frozen new PASS modules.
No historical or successful source is a compiler target.
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
BASE_MODULES = {'FriablePhysicalPrefix.lean', 'FriableEulerRankin.lean',
                'FriablePrimeHarmonic.lean', 'FriableTotientEnvelope.lean',
                'FriableKernelEnvelope.lean', 'FriablePhysicalPayment.lean'}
MODULES = ['FriableDemandAggregation.lean']
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def now(): return datetime.now(timezone.utc).isoformat()
def save_new(p, data):
    with p.open('x', encoding='utf-8') as h:
        h.write(json.dumps(data, indent=2, ensure_ascii=False)+'\n')
if len(sys.argv) != 3:
    raise SystemExit('Require extension target and explicit phase4 gate path')
src = (W / sys.argv[1]).resolve()
assert src.parent == W and src.name in MODULES
gate_path = Path(sys.argv[2]).resolve()
assert gate_path.exists(), 'NO LEAN: explicit extension gate absent'
gate = json.loads(gate_path.read_text(encoding='utf-8'))
assert gate['authorization'] == 'ROOT20_FORMAL4_AGGREGATION_COMPILE'
assert gate['root_authorized'] is True and gate['canonical_new_numeric_pass_inspected'] is True
assert gate['round'] == 20 and gate['node'] == '14.5' and gate['phase'] == 4
assert gate['authorized_new_modules'] == MODULES
assert gate['builder_sha256'] == sha(Path(__file__))
assert sha(W/'build.py') == '89dea53493843f1196bdcdb2fd8ad376649870db665b1e8aef532e1bd6c8616a'
base_path = W/'build_receipt.json'
assert sha(base_path) == gate['base_build_receipt_sha256']
base = json.loads(base_path.read_text(encoding='utf-8'))
assert set(base['successful_modules']) == BASE_MODULES
assert len(base['attempts']) == 16 and base['historical_source_compiles'] == 0
base_bindings = {}
for module in base['successful_modules'].values():
    for k in ['source', 'olean']:
        p = Path(module[k])
        assert sha(p) == module[k+'_sha256'], 'frozen base import changed'
        base_bindings[str(p)] = module[k+'_sha256']
extension_path = W/'extension_build_receipt.json'
assert sha(extension_path) == gate['extension_build_receipt_sha256']
extension_base = json.loads(extension_path.read_text(encoding='utf-8'))
assert set(extension_base['successful_modules']) == {'FriablePhysicalDemand.lean'}
for module in extension_base['successful_modules'].values():
    for k in ['source','olean']:
        p = Path(module[k])
        assert sha(p) == module[k+'_sha256']
        base_bindings[str(p)] = module[k+'_sha256']
assert base_bindings == gate['base_frozen_import_bindings']
assert sha(W/'build_extension.py') == '4bcaafaf97a8a9e2e107d7b333427fdd772f58b748416f777b820daf885bfefa'
numeric_bindings = gate['numeric_bindings']
assert numeric_bindings
for rel, expected in numeric_bindings.items():
    p = (B/rel).resolve()
    assert p.is_relative_to(B) and rel.startswith('round20/')
    assert sha(p) == expected, 'new canonical numerical binding changed'
assert gate['numeric_receipt_relative_path'] in numeric_bindings
actual = json.loads((B/gate['numeric_receipt_relative_path']).read_text(encoding='utf-8'))
assert actual['exit_code'] == 0
deps_path = W/'dependencies_readonly.json'
deps = json.loads(deps_path.read_text(encoding='utf-8'))['bindings']
for rel, expected in deps.items():
    assert sha(B/rel) == expected, 'historical read-only dependency changed'
assert sha(LEAN) == '8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
content = src.read_text(encoding='utf-8')
assert not re.search(r'\b(sorry|admit|native_decide|trustMe)\b', content)
assert not re.search(r'^\s*axiom\s+', content, re.M)
ledger_path = W/'aggregation_build_receipt.json'
record = json.loads(ledger_path.read_text(encoding='utf-8')) if ledger_path.exists() else {
    'round':20, 'role':4, 'attempts':[], 'historical_source_compiles':0,
    'successful_modules':{}, 'score':0, 'victory':False}
assert src.name not in record['successful_modules'], 'PASS replay prohibited'
for module in record['successful_modules'].values():
    for k in ['source','olean']:
        assert sha(Path(module[k])) == module[k+'_sha256']
if not record['attempts']:
    assert sha(src) == gate['initial_reviewed_source_sha256'][src.name]
else:
    last = record['attempts'][-1]
    assert last['exit_code'] != 0, 'only an actual compiler failure authorizes repair'
    assert sha(src) != last['snapshot_sha256'], 'unchanged FAIL replay prohibited'
n = len(record['attempts'])+1
prefix = f'aggregation_attempt{n:02d}'
snapshot = W/(prefix+'_source_PREEXEC.lean.txt')
builder = W/(prefix+'_builder_PREEXEC.py.txt')
with snapshot.open('xb') as h: h.write(src.read_bytes())
with builder.open('xb') as h: h.write(Path(__file__).read_bytes())
started = W/(prefix+'_started.json')
log = W/(prefix+'.log')
out = W/(prefix+'.olean')
env = dict(os.environ)
env['LEAN_PATH'] = ';'.join(map(str,[W,B/'round19'/'judge'/'build',
    B/'round18'/'judge'/'build',B/'round16'/'judge'/'build',B/'round13'/'role4'/'dependencies',
    *[CACHE/p/'.lake'/'build'/'lib' for p in PACKAGES]]))
env['PYTHONDONTWRITEBYTECODE'] = '1'
cmd = [str(LEAN),'-o',str(out),str(src)]
entry = {'attempt':n,'phase':'PREEXEC','started_utc':now(),'source':str(src),
    'source_sha256':sha(src),'snapshot':str(snapshot),'snapshot_sha256':sha(snapshot),
    'builder_snapshot':str(builder),'builder_snapshot_sha256':sha(builder),
    'command':cmd,'cwd':str(W),'LEAN_PATH':env['LEAN_PATH'],
    'compile_gate':str(gate_path),'compile_gate_sha256':sha(gate_path),
    'numeric_bindings':numeric_bindings,'dependency_bindings':deps,
    'base_frozen_import_bindings':base_bindings,'base_build_receipt_sha256':sha(base_path),
    'dependencies_manifest_sha256':sha(deps_path),'compiler_sha256':sha(LEAN)}
save_new(started,entry)
run = subprocess.run(cmd,cwd=W,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
with (W/(prefix+'.stdout.txt')).open('x',encoding='utf-8') as h: h.write(run.stdout)
with (W/(prefix+'.stderr.txt')).open('x',encoding='utf-8') as h: h.write(run.stderr)
with log.open('x',encoding='utf-8') as h: h.write(run.stdout+run.stderr)
entry.update({'phase':'FINISHED','finished_utc':now(),'exit_code':run.returncode,
    'started_receipt':str(started),'started_receipt_sha256':sha(started),
    'stdout':run.stdout,'stderr':run.stderr,'log':str(log),'log_sha256':sha(log),
    'olean':str(out) if out.exists() else None,'olean_sha256':sha(out) if out.exists() else None})
post_checks = {}
post_failures = []
def check_post(label, path, expected):
    try:
        actual_sha = sha(path)
    except OSError:
        actual_sha = None
    okay = actual_sha == expected
    post_checks[label] = {'path':str(path),'expected_sha256':expected,
                          'actual_sha256':actual_sha,'unchanged':okay}
    if not okay: post_failures.append(label)
check_post('source',src,entry['snapshot_sha256'])
check_post('gate',gate_path,entry['compile_gate_sha256'])
check_post('builder',Path(__file__),entry['builder_snapshot_sha256'])
check_post('original_builder',W/'build.py','89dea53493843f1196bdcdb2fd8ad376649870db665b1e8aef532e1bd6c8616a')
check_post('base_ledger',base_path,entry['base_build_receipt_sha256'])
check_post('extension_ledger',extension_path,gate['extension_build_receipt_sha256'])
check_post('extension_builder',W/'build_extension.py','4bcaafaf97a8a9e2e107d7b333427fdd772f58b748416f777b820daf885bfefa')
check_post('dependencies_manifest',deps_path,entry['dependencies_manifest_sha256'])
check_post('runtime',LEAN,entry['compiler_sha256'])
for path, expected in base_bindings.items(): check_post('base_import:'+path,Path(path),expected)
for rel, expected in numeric_bindings.items(): check_post('numeric:'+rel,B/rel,expected)
for rel, expected in deps.items(): check_post('historical:'+rel,B/rel,expected)
entry['post_integrity'] = {'all_unchanged':not post_failures,
    'failed_bindings':post_failures,'checks':post_checks}
entry['credited_pass'] = run.returncode == 0 and not post_failures and 'sorryAx' not in run.stdout+run.stderr
record['attempts'].append(entry)
if entry['credited_pass']:
    final = src.with_suffix('.olean')
    with final.open('xb') as h: h.write(out.read_bytes())
    record['successful_modules'][src.name] = {'attempt':n,'source':str(src),'source_sha256':sha(src),
        'olean':str(final),'olean_sha256':sha(final)}
ledger_path.write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps({'attempt':n,'module':src.name,'exit_code':run.returncode,
    'credited_pass':entry['credited_pass'],'post_integrity_unchanged':not post_failures,
    'source_snapshot':str(snapshot),'log':str(log)}))
print(run.stdout+run.stderr)
sys.exit(run.returncode if run.returncode != 0 else (0 if entry['credited_pass'] else 2))
