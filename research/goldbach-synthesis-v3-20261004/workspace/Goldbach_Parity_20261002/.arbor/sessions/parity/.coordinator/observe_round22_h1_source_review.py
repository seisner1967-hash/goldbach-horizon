"""Capture qualified source-only Judge review; no proof/compiler/numeric work."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/judge5/h1_source_review01'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(P/'read_catalog_receipt.json')
assert sha(P/'read_catalog_receipt.json')=='238ce6ce42537600d4df90e1e0069880038331a8474b15e7e6b7e165fae6f09b'
assert sha(P/'review.md')=='11b5cf745f50e75a10d670e55f39bb0e612902673a21bf13daa03bff41656e7f'
assert r['compiler_invocations']==r['mathematical_numeric_invocations']==0 and not r['H1_C3_certified'] and not r['victory']
for row in r['sources']: assert sha(Path(row['source']))==row['source_sha256']==sha(Path(row['review_copy']))==row['review_copy_sha256']
for row in r['documents']+r['independent_API_reads']: assert sha(Path(row['path']))==row['sha256']
assert len(r['sources'])==9 and r['main_declaration_count']==42 and r['pending_gamma_dependency_declaration_count']==31
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'receipt_sha256':sha(P/'read_catalog_receipt.json'),'report_sha256':sha(P/'review.md'),'ROOT_report_FULL_read':'0eb06c','ROOT_catalogue_scope':'Complete JSON parsed and source/copy/docs/API hashes verified; header projection only. Initial535ea2 TRUNCATED is not FULL.','source_copies_verified':9,'API_bindings_verified':len(r['independent_API_reads']),'document_bindings_verified':len(r['documents']),'main_SOURCE_declarations':42,'pending_Gamma_SOURCE_declarations':31,'compiled_Gamma_dependency_declarations_not_new_credit':23,'Lambda14_aval':'SOURCE author file1a08c225 remains outside this Judge review','known_subsequent_API_risk':'ROLE4 identified integral_const_mul in uncompiled GammaContourComponent; fix in distinct revision, no actual compiler FAIL','ROLE3_dispatch':'/root/round22_formal3_prepare SOURCE h1_psi/P1/C5; ROLE4 continues Euler/Mellin-series','numeric_H1_certified':False,'H1_formal_certified':False,'D_N_paid':False,'WIN':False,'official_modules':62,'official_auxiliaries':1049,'root_compiler_invocations':0,'root_numeric_invocations':0}
with (C/'messages/round22_h1_source_review_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_H1_EULER_MELLIN_PSI_C5_AND_NUMERIC_COMPONENT_SOURCES_PARALLEL'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_h1_source_review_observation.json','round22/judge5/h1_source_review01/review.md']
for actor in cp['in_flight_executors']:
    if actor['role']==5: actor['status']='BATCH02_AUX_PASS_AND_H1_SOURCE_REVIEW_CLOSED_NO_REPLAY'
    if actor['role']==3: actor['status']='G0_INDEPENDENT_CERTIFIED_REACTIVATED_H1_PSI_C5_SOURCE_ONLY'; actor['agent']='/root/round22_formal3_prepare'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
