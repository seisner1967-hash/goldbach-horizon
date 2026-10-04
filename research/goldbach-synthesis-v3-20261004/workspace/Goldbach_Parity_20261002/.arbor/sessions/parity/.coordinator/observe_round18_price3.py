"""Inspect actual stored price-module attempts04/05 only."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,re
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';R=B/'round18/role3'
def digest(p):return sha256(p.read_bytes()).hexdigest()
rows=[]
for n in [4,5]:
 r=json.loads((R/f'attempt{n:02d}_receipt.json').read_bytes())
 assert r['exit_code']==(1 if n==4 else 0)
 assert r['source_sha256']==r['snapshot_sha256']==digest(Path(r['source_snapshot']))
 assert r['builder_sha256']==digest(Path(r['builder_snapshot']))
 assert r['log_sha256']==digest(Path(r['log']))
 body=Path(r['source_snapshot']).read_text(encoding='utf-8').split('-- AXIOM_AUDIT_BEGIN')[0]
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|trustMe)\b',body)
 log=Path(r['log']).read_text(encoding='utf-8')
 rows.append(dict(attempt=n,exit_code=r['exit_code'],source_snapshot_sha256=r['snapshot_sha256'],log_sha256=r['log_sha256'],
  errors=log.count(': error:'),warnings=log.count(': warning:'),failed_log_generated_sorryAx='sorryAx' in log))
src=R/'SeparatedTypeIIPrice.lean'
assert digest(src)==r['source_sha256']=='dd971712c281236332d272e645498b6ace83b6b6a80915b5f6bca4fa8cc2551c'
assert digest(Path(r['olean']))==digest(Path(r['preserved_olean']))==r['olean_sha256']=='4d93de985a4e7dc95fbc49bd045315c8be18c5e2dee1b2e8afafacb394c41ac2'
assert ': error:' not in log and ': warning:' not in log and 'sorryAx' not in log
decls=re.findall(r'^(theorem|def)\s+(\w+)',body,re.M)
assert [name for _,name in decls]==r['new_declarations']
prints=[]
for name,_,axioms in re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log):
 assert all(a.strip() in {'propext','Classical.choice','Quot.sound'} for a in axioms.split(',') if a.strip())
 prints.append(name.rsplit('.',1)[-1])
assert prints==r['new_declarations'] and len(prints)==14
result=dict(status='ROOT_INSPECTED_AUTHOR_PRICE18_PASS05_JUDGE_PENDING',actual_attempts=rows,
 declarations={k:sum(kind==k for kind,_ in decls) for k in ['theorem','def']},standard_axiom_prints=14,
 mathematical_content='real weighted product sums and inverse reindexing; full II calibration price, distinct raw/theta difference, actual factorized-product theta zero under independent candidate front',
 Gamma_or_global_D_N_estimated=False,independent_judge_completed=False,root_reran_Lean_or_producer_or_audit=False,victory=False)
with (C/'messages/round18_price3_root_observation.json').open('x',encoding='utf-8') as h:json.dump(result,h,indent=2);h.write('\n')
p=C/'checkpoint.json';cp=json.loads(p.read_bytes());cp['last_progress']+=' Separateprice18 authorattempt04exit1(simp/no-progress+unusedvariable),05exit0; fullyrootreadsource/logs/receipts and source/snap/olean14standardprintsbound. Elevenauxiliarytheorems3defs, no oldcorePASS recompile. IndependentJudgepending and wholeGamma/globalD_N notestimated.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/role3/SeparatedTypeIIPrice.lean','round18/role3/attempt04_receipt.json','round18/role3/attempt05_receipt.json','.arbor/sessions/parity/.coordinator/messages/round18_price3_root_observation.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(result))
