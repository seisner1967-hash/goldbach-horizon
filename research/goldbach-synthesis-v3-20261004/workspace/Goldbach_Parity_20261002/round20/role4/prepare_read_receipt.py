"""Durable metadata of actual reading scopes. No mathematical producer or Lean."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
W=Path(__file__).resolve().parent
B=W.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pre=json.loads((W/'preparation.json').read_text(encoding='utf-8'))
primary=[]
for path,expected in pre['inputs'].items():
    p=Path(path)
    assert sha(p)==expected
    scope='FULL_TEXT_READ'
    if p.name=='round20_role2_selection.json':
        scope='FULL_STRUCTURED_METADATA_AND_DUPLICATE_EXECUTOR_PROMPT_READ_SEPARATELY'
    primary.append({'path':str(p),'sha256':expected,'scope':scope})
skill_root=Path(r'C:\Users\Utilisateur\.codex\skills')
skills=[]
for name in ['arbor-agent-executor','arbor-agent-merge-eval']:
    p=skill_root/name/'SKILL.md'
    skills.append({'path':str(p),'sha256':sha(p),'scope':'FULL_TEXT_READ'})
partial=[
 ('round19/judge/build/NonSSBracketSwitch.lean','FULL_TEXT_READ'),
 ('round19/judge/build/BalancedResourceSwitch.lean','PARTIAL_FIRST_100_LINES'),
 ('round13/role4/dependencies/ThreeAdicPrimePairing.lean','PARTIAL_FIRST_84_LINES'),
 ('round13/role4/dependencies/ShortDivisorComplement.lean','PARTIAL_LINES_1_38_AND_141_184')]
dependencies=[{'path':str(B/rel),'sha256':sha(B/rel),'scope':scope} for rel,scope in partial]
gates=[]
for phase in [1,2,3]:
    p=B/f'.arbor/sessions/parity/.coordinator/messages/round20_formal4_authorization_phase{phase}.json'
    gates.append({'path':str(p),'sha256':sha(p),'scope':'FULL_TEXT_READ'})
data={'round':20,'role':'logicalROLE4','node':'14.5','at_utc':datetime.now(timezone.utc).isoformat(),
 'primary_inputs':primary,'skills':skills,'dependency_source_scopes':dependencies,'compile_gates':gates,
 'historical_dependency_manifest':{'path':str(W/'dependencies_readonly.json'),
    'sha256':sha(W/'dependencies_readonly.json'),'scope':'18_BINDINGS_HASH_CHECKED_NOT_18_FULL_SOURCE_READS'},
 'mathlib_reads':'Targeted actual API excerpts: smoothNumbers, finite Euler, arithmetic multiplicativity/tau, totient, squarefree divisors, geometric HasSum, harmonic bounds, p-series, integrals, inverse/order, finite sums and Nat.ModEq.',
 'mutable_idea_tree':'observation only; no frozen input substitution',
 'old_producer_reexecution':False,'old_Lean_reexecution':False,'new_mathematical_python':0,'victory':False}
with (W/'read_input_sha256.json').open('x',encoding='utf-8') as h:
    h.write(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'primary_bindings':len(primary),'reading_scopes_recorded':True,'mathematical_executions':0}))
