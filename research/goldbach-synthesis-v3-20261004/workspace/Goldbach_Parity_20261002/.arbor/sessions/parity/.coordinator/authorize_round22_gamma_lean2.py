"""Authorize one Gamma source repair; byte and declaration metadata only."""
import json, hashlib, re
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; O=B/'round22/role4'; P=O/'revision01'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def headers(p): return [re.sub(r'\s+',' ',m.group(0)).strip() for m in re.finditer(r'^(?:theorem|def)\s+\w+\b.*?:=',p.read_text(encoding='utf-8'),re.MULTILINE|re.DOTALL)]
mp=P/'gamma_prepared_manifest4.json'; m=read(mp)
assert sha(mp)=='016bb67767b61cbf15fbaf679a3e435bc9e88d4053f26873e4557b4727ba1f9b'
assert m['status']=='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED' and len(m['immutable_inputs'])==6415 and not m['unresolved_modules']
assert m['previous_actual_exit']==1 and m['new_compiler_invocations_authorized']==0 and not m['win']
for e in m['immutable_inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert sha(P/'GammaPrerequisites22.lean')==m['source_sha256']=='c66707c8bf24428e80ccc9000a769790d19d734d00cff0efe1e807364acb10fc'
assert sha(P/'run_gamma_once22_v4.py')==m['launcher_sha256']=='eb0c2268fe1f5f9c51ae2b03bd4a9e8a1419f003a2613a0282c33f2b0634e711'
assert headers(O/'GammaPrerequisites22.lean')==headers(P/'GammaPrerequisites22.lean') and len(headers(P/'GammaPrerequisites22.lean'))==23
failure=O/'gamma_attempt1/receipt.json'; assert sha(failure)==m['previous_actual_receipt_sha256']=='85f95efc916eb5de022ac8a4ca79f82d5d2df1c717cc1bf216fd2a927c80db45'
assert read(failure)['exit_code']==1 and read(C/'messages/round22_gamma_failure01_observation.json')['copies_verified']==8
gate=read(C/'messages/round22_gamma_role4_authorization1.json'); bank=Path(gate['informative_gamma_bank_path'])
assert sha(bank)==gate['informative_gamma_bank_sha256'] and read(bank)['status']==gate['informative_gamma_bank_status']=='GAMMA_ROTATED_LAPLACE_AUX_PASS'
assert not (P/'gamma_attempt2').exists()
gate.update({'schema':'ROUND22_ROLE4_GAMMA_H2_LEAN_AUTHORIZATION_2','created_utc':datetime.now(timezone.utc).isoformat(),'prepared_manifest_sha256':sha(mp),'source_sha256':m['source_sha256'],'revised_source_sha256':m['source_sha256'],'launcher_sha256':m['launcher_sha256'],'verified_immutable_inputs':6415,'previous_failure_receipt_sha256':sha(failure),'unchanged_statements_gamma_bank_compatibility_verified':True,'source_statement_metadata_comparison':'All 23 whitespace-normalized declaration headers identical; definitions/theorem domains unchanged; no numerical replay.','root_FULL_reads':{'source':'2ac6fb','launcher':'c886c6','preparation':'ac925a','metadata_builder':'ab9245','reads':'de20a1','previous_failure_diagnosis':'941e7f','previous_log':'b1f5c1','previous_receipt':'5ad642'},'manifest_read_scope':'Complete JSON parsed and 6415 input bytes verified; header projection only, not FULL whole text.'})
gp=C/'messages/round22_gamma_role4_authorization2.json'
with gp.open('x',encoding='utf-8') as f: json.dump(gate,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_SECOND_AUTHOR_COMPILE_AUTHORIZED_JUDGE_BATCH01_PASS_OBSERVATION_PENDING'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_gamma_role4_authorization2.json']
for actor in cp['in_flight_executors']:
    if actor['role']==4: actor['status']='GAMMA_REVISION01_ONE_AUTHOR_COMPILE_AUTHORIZED_NOT_STARTED'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'manifest_HEADER_projection':{k:v for k,v in m.items() if k!='immutable_inputs'},'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':6415,'root_compiler_invocations':0,'WIN':False},ensure_ascii=False,indent=2))
