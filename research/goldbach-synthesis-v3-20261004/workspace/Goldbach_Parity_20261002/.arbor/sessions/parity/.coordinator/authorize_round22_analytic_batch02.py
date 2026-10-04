"""ROOT byte bindings only; author batch with two readonly judged dependencies."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/role4/h1_contour/analytic_batch02'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
mp=P/'prepared_manifest22.json';m=read(mp)
assert sha(mp)=='5656d1e9ba961207c15a0c9f5bbac13b572d73e337cf1e3524d8e89989ba3e9e'
assert sha(P/'run_analytic_batch_once22.py')=='d9658ba41563e135bd85decb95ceb6aeae90a22cb7eef8444fac77c6aadf4b10'
assert sha(P/'read_receipts22.json')=='f965d48774f733d2262d404d7b5f32b90751c782a855e0bc7b4f32c9b867fc2f'
assert m['status']=='PREPARED_SOURCE_ONLY_COMPILER_GATE_CLOSED' and m['new_lean_invocations']==m['new_mathematical_python_invocations']==0
assert len(m['immutable_inputs'])==6524 and m['import_module_count']==len(m['import_graph'])==3250 and m['unresolved_modules']==[]
assert m['declaration_count']==39 and [x['module'] for x in m['modules']]==['GammaBoxBounds22','GammaContourComponent22','MellinThermal22','MellinThermalInversion22']
assert [x['source_sha256'] for x in m['modules']]==['4874192b1c2ca9edc7262d8a46f9d4a1e339c565e5bb48fefbf4d6d100071edf','244f20f0d0198101b6b2a27841b273b01f7c52f28a38b7b51b4db588446f4265','1396cb0a0045c621ea3e8f0f8b905c1c2a0af3ec33a351e4e7150542f38352fe','ad42b7bf8cd9b94e4f2c04125201b6a82b62821b1cb38652aa4e2f6c41a1df66']
for x in m['immutable_inputs']:assert sha(Path(x['path']))==x['sha256'],x['path']
assert {x['module'] for x in m['judged_dependencies']}=={'GammaPrerequisites22','GammaDerivative22'}
for x in m['judged_dependencies']:
 fin=read(Path(x['independent_fin_path']));assert fin['status']=='INDEPENDENT_LEAN_AUX_PASS' and fin['exit_code']==0
 assert fin['source_sha256']==sha(Path(x['staged_source_path'])) and fin['olean_sha256']==sha(Path(x['staged_olean_path']))
archives=read(B/'round22/previous_artifacts_sha256.json');assert archives['file_count']==3089
for rel,digest in archives['sha256'].items():assert sha(B/rel)==digest,rel
assert not (P/'actual_attempt01').exists()
g={'schema':'ROUND22_ROLE4_ANALYTIC_BATCH02_AUTHORIZATION_1','authorized':True,'role':'ROLE4','node_id':'15.3',
 'created_utc':datetime.now(timezone.utc).isoformat(),'compiler_invocations_max':4,'stop_first_failure':True,'no_retry':True,
 'prepared_manifest_sha256':sha(mp),'launcher_sha256':sha(P/'run_analytic_batch_once22.py'),'modules':[x['module'] for x in m['modules']],
 'ROOT_FULL_reads':{'launcher':'b79ce6','builder':'973a5c','preparation':'f4fcbc','read_receipts':'1359d9',
 'Box_Contour_corrected':'629aa7','Mellin_identical_prior':'3eb9a0','Inversion_identical_prior':'15e2fa'},
 'metadata_scope':'Complete JSON parsed,6524boundbytes/3250importheaders/3089archives verified; no FULL raw manifest/allcachemath claim',
 'inputs_verified':6524,'archives_verified':3089,'new_numeric_invocations':0,'root_compiler_invocations':0,
 'numeric_PASS_required':False,'readonly_judged_dependencies_recompile':False,'H1_paid':False,'D_N_paid':False,'WIN':False}
gp=C/'messages/round22_role4_analytic_batch02_authorization1.json'
with gp.open('x',encoding='utf-8') as f:json.dump(g,f,ensure_ascii=False,indent=2);f.write('\n')
cpp=C/'checkpoint.json';cp=read(cpp);cp['phase']='ROUND22_ANALYTIC02_FOUR_AUTHOR_CHILDREN_AUTHORIZED_PSI04_RUNNING_CORE_JUDGE_PREPARING'
for a in cp['in_flight_executors']:
 if a['role']==4:a['status']='ANALYTIC02_FOUR_AUTHOR_CHILDREN_AUTHORIZED_NOT_STARTED'
cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate_path':str(gp),'gate_sha256':sha(gp),'verified_inputs':6524,'verified_archives':3089,'root_compiler_invocations':0,'root_numeric_invocations':0,'WIN':False},indent=2))
