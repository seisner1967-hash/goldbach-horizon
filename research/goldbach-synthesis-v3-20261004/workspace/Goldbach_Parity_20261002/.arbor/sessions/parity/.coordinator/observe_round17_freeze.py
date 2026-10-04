"""Coordinator verifies frozen Judge inputs only; no authors/compiler/audit run."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
R=B/'round17'
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
p=R/'judge/input_sha256.json'; j=json.loads(p.read_bytes())
assert digest(p)=='40076625c36a04c5cef48ece8ee2d4fe625715cfbe1bf06364ae3da5b182bcb1'
assert j['files']==len(j['sha256'])==143
for rel,h in j['sha256'].items():assert digest(R/rel)==h,rel
for name,h in j['external_originals_sha256'].items():assert digest(Path(name))==h,name
for name,h in j['fixed_contexts_sha256'].items():assert digest(Path(name))==h,name
for rel,h in j['final_role_signals'].items():assert j['sha256'][rel]==h
assert digest(Path(j['lean_executable']))==j['lean_sha256']
assert j['all_FINAL_notifications_received'] and not j['producer_or_Lean_executed']
obs=dict(status='ROOT_VERIFIED_INDEPENDENT_JUDGE_FROZEN_INPUTS',input_manifest_sha256=digest(p),
         author_inputs=143,initial_numeric_bindings=33,distinct_C4_bindings=15,protected_previous=799,
         originals_and_contexts_bound=True,producer_Lean_or_Judge_audit_reran_by_root=False,victory=False)
(C/'messages/round17_root_input_freeze_observation.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=json.loads(p.read_bytes())
cp['phase']='ROUND17_INDEPENDENT_INPUTS_FROZEN_JUDGE_PREPARING_UNIQUE_AUDIT'
cp['in_flight_executors']=['round17_judge: actual independent input freeze143 complete; unique audit launcher and fresh five-module compiler preparation active']
cp['last_progress']+=' Independent Judge freeze143 actual, root verifies all author/original/context/compiler SHA bindings, no audit or compiler rerun. Unique fresh audit still awaits actual launch; no verdict presumed.'
cp['previous_goal_turn_evidence']+=['round17/judge/input_sha256.json','.arbor/sessions/parity/.coordinator/messages/round17_root_input_freeze_observation.json']
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs))
