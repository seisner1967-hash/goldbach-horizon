"""Coordinator binding verification only; no numerical or Lean producer."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,re
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
R=B/'round17/role3'
def digest(p): return sha256(p.read_bytes()).hexdigest()
p=R/'final_receipt.json';r=json.loads(p.read_bytes())
assert digest(p)=='b0e77208bfad5aaf3792de8424922d0945281e2dd77ff74c20efd9b7943031b4'
for k,hk in [('source','source_sha256'),('olean','olean_sha256'),('report','report_sha256'),('last_log','last_log_sha256')]:
 assert digest(Path(r[k]))==r[hk]
for f in r['files']: assert digest(Path(f['path']))==f['sha256']
for n,h in r['input_bindings'].items(): assert digest(Path(n))==h
assert r['theorem_count']==len(r['theorems'])==42
assert r['definition_count']==len(r['definitions'])==23
log=Path(r['last_log']).read_text(encoding='utf-8')
for a in re.findall(r'depends on axioms: \[([^\]]*)\]',log):
 assert set(re.findall(r'[A-Za-z_.]+',a)) <= {'propext','Classical.choice','Quot.sound'}
assert not re.search(r'(?i)error|warning|sorryAx',log)
assert r['compilatory_invocations']==14 and r['actual_exit1_count']==12
assert r['successful_candidate_attempts']==[11,14]
obs=dict(status='ROOT_VERIFIED_FROZEN_FINAL3_AWAITING_JUDGE',source_sha256=r['source_sha256'],
 report_sha256=r['report_sha256'],receipt_sha256=digest(p),theorems=42,definitions=23,
 actual_attempts=14,real_technical_failures=12,producer_passes=[11,14],root_reran_Lean=False,victory=False)
(C/'messages/round17_root_final3_observation.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';j=json.loads(p.read_bytes())
j.update(phase='ROUND17_FINAL3_C4_FORMAL_AND_NUMERIC_ANNEX_JUDGE_PREPARATION')
j['in_flight_executors']=[
 'round13_bilateral_ideation: role4 core8 frozen, PowersetMoment/FourFormTruncation partial PASS, collision loss under development',
 'round13_formal3_switch: role6 C4 new numeric annex actual startup and canonical process78617 confirmed, initial FINAL6 frozen',
 'round17_judge: independent read-only preparation; awaits FINAL4 and FINAL6_C4 before unique audit']
j['last_progress']+=' FINAL3 fully read with exact source11-to14 diff and logs12/13/14. Root verifies every receipt file/input binding and42theorems23defs/standardaxioms,14attempts12technicalfailures/PASS11,14. C4 finite moment contract confirmed by4 and delegated separately to6: new subset moment/queue/Markov on16 unsaturated cores, P2/3/5/7,z100; half-moment condition evaluated, false retained. Initial33 numericbindings immutable. Old3handle dispatch failed without launch; listed6 followup succeeded and actual canonical process78617 confirmed. One root shell SpawnChild access failure retried by safe read successfully, no math execution. Judge waits FINAL4/FINAL6_C4. No source C4/C6 or victory.'
for n in ['round17/agent3_formalisation.md','round17/role3/final_receipt.json','.arbor/sessions/parity/.coordinator/messages/round17_root_final3_observation.json']:
 if n not in j['previous_goal_turn_evidence']:j['previous_goal_turn_evidence'].append(n)
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs))
