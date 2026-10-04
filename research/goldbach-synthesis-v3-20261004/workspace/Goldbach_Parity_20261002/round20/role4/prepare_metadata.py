"""Metadata preparation only; imports no numerical producer or compiler."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
W = Path(__file__).resolve().parent
B = W.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save_new(p,data):
    with p.open('x',encoding='utf-8') as h:
        h.write(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
old = json.loads((B/'round19/role4/dependencies_readonly.json').read_text(encoding='utf-8'))
bindings = dict(old['bindings'])
for rel, expected in bindings.items():
    assert sha(B/rel) == expected
for name in ['TerminalPrimeExtraction','BalancedResourceSwitch','SignedHyperbolicCRT','NonSSBracketSwitch']:
    for suffix in ['lean','olean']:
        rel = f'round19/judge/build/{name}.{suffix}'
        bindings[rel] = sha(B/rel)
save_new(W/'dependencies_readonly.json',{
    'round':20,'role':4,'mode':'read-only audited Judge19/18/16/13 imports; no historical source compiles',
    'bindings':bindings,'dependency_theorems_recounted':False})
inputs = [B/'round20/PROBE_BLOCK.md', B/'round20/agent2_friable.md',
    B/'round20/role2/numeric_contract.md', B/'round20/role2/final_receipt.json',
    B/'.arbor/sessions/parity/.coordinator/messages/round20_role2_selection.json',
    B/'.arbor/sessions/parity/experiments/14.5/executor_prompt.md']
save_new(W/'preparation.json',{
    'status':'SOURCE_AND_LAUNCHER_PREPARATION_ONLY_NO_COMPILER_INVOCATION',
    'at_utc':datetime.now(timezone.utc).isoformat(),'round':20,'role':4,'node':'14.5',
    'inputs':{str(p):sha(p) for p in inputs},
    'dependencies_manifest_sha256':sha(W/'dependencies_readonly.json'),
    'builder_sha256':sha(W/'build.py'),
    'numeric_PASS_not_yet_inspected_here':True,'compile_authorization_absent':True,
    'new_sources_at_preparation':{p.name:sha(p) for p in W.glob('*.lean')},
    'historical_source_compiles':0,'victory':False})
print(json.dumps({'status':'metadata prepared','historical_bindings':len(bindings),
                  'new_Lean_invocations':0,'victory':False}))
