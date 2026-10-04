"""ROOT immutable byte checks and gate only; no compiler/numerical execution."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator'
P=B/'round22/judge5/batch03'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
expected={'prepared_manifest.json':'9213cfc197ce5f594005f4fdfbd7ff88b1dd54cc216c14fdfd6cb801089bd86d',
 'run_once.py':'bf81956b2328f7b6a84faee912d3332327906491b4fc6ebcd6da1dcb8fdc711f',
 'prepare_metadata.py':'e4b73b5b1153a21ad54baf719b3594b57035c264d1235ae1ecaf7b828d7460c8',
 'prepared_receipt.json':'2e21cb47c6d53ea9cd5a1c1041acd324accaddd8070666f50f19e0b44c9ec8d6',
 'read_receipts.json':'897c4f853b084ba88926b0eefde62f776080da13745108079d8cc58b3703645f',
 'catalog.json':'0b0596ccd339972fdf86e0414ca6f2e6935d9201b010cc33e984373326f2ab7a',
 'closed_judge_bindings.json':'f7abb8b461c5efd2b7eb19bcccf77c0185ae01451905c52ee1d875359aa1e86c',
 'import_bindings.json':'13af0cb58ef7f51fa20067ae03540fb8ff1362bf2b9d1e650231e513f3744008',
 'preparation.md':'b3601e7b3dbd5f2311aeb9234ebb2e6c4f4f9f4d567c5cd2c620f9659c741bda'}
for name,digest in expected.items():assert sha(P/name)==digest,name
m=read(P/'prepared_manifest.json');cat=read(P/'catalog.json');imports=read(P/'import_bindings.json');old=read(P/'closed_judge_bindings.json')
assert m['status']=='PREPARED_SOURCE_ONLY_GATE_CLOSED' and m['modules']==['GammaDerivative22']
assert m['compiler_invocations']==m['mathematical_numeric_invocations']==0
assert len(m['immutable_inputs'])==6597 and m['unresolved_modules']==[]
assert len(imports['entries'])==imports['module_count']==3235 and imports['unresolved']==[]
assert any(r['module']=='Init' for r in imports['entries'])
assert len(old['inputs'])==m['closed_judge_files']==90
assert cat['module_count']==1 and cat['total_declarations']==8
assert cat['modules'][0]['source_sha256']=='026ced6097c7d658b41501254bfbcdefe86ff2e68fb9fbe3fab01023a4cb0975'
for r in m['immutable_inputs']:assert sha(Path(r['path']))==r['sha256'],r['path']
for r in old['inputs']:assert sha(Path(r['path']))==r['sha256'],r['path']
archives=read(B/'round22/previous_artifacts_sha256.json');assert len(archives['sha256'])==archives['file_count']==3089
for rel,digest in archives['sha256'].items():assert sha(B/rel)==digest,rel
assert not (P/'batch03_attempt01').exists()
gate={'schema':'ROUND22_JUDGE5_BATCH03_AUTHORIZATION','role':'ROLE5','authorized':True,
 'attempt':'batch03_attempt01','modules':['GammaDerivative22'],'compiler_invocations_maximum':1,
 'source_manifest_sha256':expected['prepared_manifest.json'],'launcher_sha256':expected['run_once.py'],
 'preparation_receipt_sha256':expected['prepared_receipt.json'],
 'python_sha256':'4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c',
 'lean_sha256':'8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08',
 'readonly_batch02_dependency_directory':str(B/'round22/judge5/batch02_attempt01'),
 'independent_audit':True,'author_olean_allowed':False,'no_win':True,
 'created_utc':datetime.now(timezone.utc).isoformat(),'inputs_verified':6597,'old_judge_files_verified':90,'archives_verified':3089,
 'root_FULL_reads':{'launcher':'bad2ed','builder':'689b3c','preparation':'7fef05_complete_preparation_tail_only',
 'prepared_receipt':'9f59a2','read_receipts':'3e93d2','source_identical_prior':'8e198f'},
 'manifest_read_scope':'Complete JSON parsed and all6597 inputs hashed; no FULL raw manifest or all-import mathematical claim',
 'numeric_PASS_required':False,'root_compiler_invocations':0,'root_numeric_invocations':0}
gp=C/'messages/round22_judge5_batch03_authorization.json'
with gp.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json';cp=read(cpp);cp['phase']='ROUND22_JUDGE_GAMMA_DERIVATIVE_ONE_CHILD_AUTHORIZED_PSI03_CORE_AUTHOR_PASS_BETA_FAIL'
for a in cp['in_flight_executors']:
 if a['role']==5:a['status']='BATCH03_GAMMA_DERIVATIVE_ONE_INDEPENDENT_CHILD_AUTHORIZED_NOT_STARTED'
 if a['role']==3:a['status']='PSI03_CORE_AUTHOR_PASS19_BETA_FAIL_PSI04_THREE_MODULE_SOURCE'
 if a['role']==4:a['status']='ANALYTIC_BATCH02_SOURCE_SELECTED_GAMMA_DEPENDENCY_JUDGE_PENDING'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'inputs_verified':6597,'imports':3235,
 'old_judge_files_verified':90,'archives_verified':3089,'compiler_invocations':0,'numeric_invocations':0,'WIN':False},indent=2))
