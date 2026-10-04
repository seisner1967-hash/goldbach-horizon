"""Authorize one Gamma source repair; byte and declaration metadata only."""
import json, hashlib, re
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; O=B/'round22/role4'; P=O/'revision02'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def headers(p): return [re.sub(r'\s+',' ',m.group(0)).strip() for m in re.finditer(r'^(?:theorem|def)\s+\w+\b.*?:=',p.read_text(encoding='utf-8'),re.MULTILINE|re.DOTALL)]
mp=P/'gamma_prepared_manifest5.json'; m=read(mp)
assert sha(mp)=='a44df37751101863d8da221d5a30e0024a049a9f4d1260c86ae0e8b3bdf37c9d'
assert m['status']=='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED' and len(m['immutable_inputs'])==6442 and not m['unresolved_modules']
assert m['previous_actual_exit']==1 and m['new_compiler_invocations_authorized']==0 and not m['win']
for e in m['immutable_inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert sha(P/'GammaPrerequisites22.lean')==m['source_sha256']=='9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7'
assert sha(P/'run_gamma_once22_v5.py')==m['launcher_sha256']=='4ed2b6f92eb9b7ad2a42e2cbe56153ce48646e196edc5d6ee087078547846096'
assert headers(O/'GammaPrerequisites22.lean')==headers(P/'GammaPrerequisites22.lean') and len(headers(P/'GammaPrerequisites22.lean'))==23
failure=O/'revision01/gamma_attempt2/receipt.json'; assert sha(failure)==m['previous_actual_receipt_sha256']=='5ebfd56de12c3b3e01342a3dbf73690a5a24c66a9d1eb11aa1e449b6c8e8070f'
assert read(failure)['exit_code']==1 and read(C/'messages/round22_gamma_failure02_observation.json')['copies_verified']==13
gate=read(C/'messages/round22_gamma_role4_authorization2.json'); bank=Path(gate['informative_gamma_bank_path'])
assert sha(bank)==gate['informative_gamma_bank_sha256'] and read(bank)['status']==gate['informative_gamma_bank_status']=='GAMMA_ROTATED_LAPLACE_AUX_PASS'
assert not (P/'gamma_attempt3').exists()
gate.update({'schema':'ROUND22_ROLE4_GAMMA_H2_LEAN_AUTHORIZATION_3','created_utc':datetime.now(timezone.utc).isoformat(),'prepared_manifest_sha256':sha(mp),'source_sha256':m['source_sha256'],'revised_source_sha256':m['source_sha256'],'launcher_sha256':m['launcher_sha256'],'verified_immutable_inputs':6442,'previous_failure_receipt_sha256':sha(failure),'unchanged_statements_gamma_bank_compatibility_verified':True,'source_statement_metadata_comparison':'All 23 whitespace-normalized declaration headers identical; definitions/theorem domains unchanged; no numerical replay.','root_FULL_reads':{'source':'aa39bb','launcher_preparation_reads':'8ef23f','metadata_builder':'ecd70f','previous_log':'61c915','previous_receipt':'d5da3f+6b655b'},'manifest_read_scope':'Complete JSON parsed and 6442 input bytes verified; header projection only, not FULL whole text.'})
gp=C/'messages/round22_gamma_role4_authorization3.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_THIRD_AUTHOR_COMPILE_AUTHORIZED_UNFOLD_AUTHOR_PASS_JUDGE_PENDING'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_gamma_role4_authorization3.json']
for actor in cp['in_flight_executors']:
    if actor['role']==4: actor['status']='GAMMA_REVISION02_ONE_AUTHOR_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'manifest_HEADER_projection':{k:v for k,v in m.items() if k!='immutable_inputs'},'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':6442,'root_compiler_invocations':0,'WIN':False},ensure_ascii=False,indent=2))
