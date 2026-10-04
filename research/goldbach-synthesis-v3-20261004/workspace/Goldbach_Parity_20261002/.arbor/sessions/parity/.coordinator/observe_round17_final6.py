"""Root frozen numeric manifest verification, no bank/Lean invocation."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');R=B/'round17';C=B/'.arbor/sessions/parity/.coordinator'
def read(p):return json.loads(p.read_bytes())
def digest(p):
 h=sha256()
 with p.open('rb') as f:
  for x in iter(lambda:f.read(1048576),b''):h.update(x)
 return h.hexdigest()
expect={'agent6.md':'629f3ea869c027919970544edf68e9701d8fe3a6d9336a52994d34e1178328af','numeric_manifest.json':'c6e1efe0ef1e4c2448bb9d53eb6df1635b29eb9a077723620ce62d4f45a6b1e4','role6_final_receipt.json':'6c93e033570fe13e7fe930f947387fc267b9e229b328c03dc171bc96c9e0b8fb'}
for n,h in expect.items():assert digest(R/n)==h,n
m=read(R/'numeric_manifest.json');r=read(R/'role6_final_receipt.json')
assert m['files']==len(m['sha256'])==33 and r['own_assets_before_receipt']==len(r['own_assets_sha256'])==32
for n,h in m['sha256'].items():assert digest(R/n)==h,n
assert r['own_assets_sha256']=={n:h for n,h in m['sha256'].items() if n!='role6_final_receipt.json'}
assert r['interval_certificate_positions']==390 and r['real_failed_numeric_attempts']==1 and r['isolated_replays']==2
assert r['new_Lean_modules_by_this_role']==0 and not r['victory']
for n,h in r['reports_FINAL_sha256'].items():assert digest(R/n)==h,n
obs={'status':'ROOT_VERIFIED_FINAL6_AND_ALL33_NUMERIC_BINDINGS','frozen_sha256':expect,'all33_bindings_verified':True,'interval_positions':390,'failures':1,'isolated_replays':2,'root_reran_math_producer':False,'root_reran_Lean':False,'victory':False}
(C/'messages/round17_root_final6_observation.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';j=read(p);j.update(phase='ROUND17_NUMERIC_FINAL_JUDGE_READONLY_PREPARATION_FORMAL_C4_ACTIVE')
j['in_flight_executors']=[
 'round17_formal3_selberg: role3 actual-rho Selberg and real Mobius bridge extension, core11 PASS, awaiting FINAL',
 'round13_bilateral_ideation: role4 FourFormRoots core8 PASS/frozen, separate C4 truncation extension awaiting FINAL',
 'round17_judge: role5 independent read-only preparation on fixed FINAL1/2/6; waits FINAL3/4 before unique audit/fresh new Lean']
j['last_progress']+=' FINAL6 source/report/finalizer execution portions and manifest/receipt schemas reviewed; root independently verifies all33 numericbindings, FINAL1/2/addendum hashes and 390 stored sign positions metadata. Fresh independent Judge17 dispatch succeeded and its actual preparation confirmed; no audit or compiler launched by Judge yet. Both formalizers continue quantitative raccord/C4, no external blocker.'
j['previous_goal_turn_evidence']+=['round17/agent6.md','round17/numeric_manifest.json','round17/role6_final_receipt.json','.arbor/sessions/parity/.coordinator/messages/round17_root_final6_observation.json']
p.write_text(json.dumps(j,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs))
