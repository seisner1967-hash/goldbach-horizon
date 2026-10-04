"""ROOT pure metadata gate for two new independent auxiliary Lean children."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/judge5/batch05'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
expected={'prepared_manifest.json':'2d878cac720a4b12de8cc0e7f9f6eafa87f4d14f3cd5ff13ff86e06e542f2743',
 'run_once.py':'5209336d77f3c4a85a420a9e9fd4193cd9a677328279920a6be78c635cf73147',
 'prepare_metadata.py':'305c67c1f315f7cc30ddb70f524676a00ec968138109762b9a1f15d3e05046c4',
 'preparation.md':'0e77ec31765f26dc206a74d0d956d2a2e69bf79306051f1bf495db7f3aa6ee78',
 'catalog.json':'45ae07f253cdd85e6f2cc5ef8a4dcfff658d4ecde5b40f10168ab3f750227818',
 'read_receipts.json':'b38fcb7d9d51eaa681a19d6094736da50b537e30f038d68dae0e59ddf347562f',
 'prepared_receipt.json':'8980b407f46f1a1f5344bea6a5db993827037e3bba3c10b2c93b2c5dfce3f6d5',
 'import_bindings.json':'aed5245c632496ec1d8b2d3bb396c86699e19f24245d01d006f637bd292e7eb8',
 'closed_judge_bindings.json':'0824b8ea6ac85ab7f709e92654394cdc3d5aa4d9a56191c06f62d7b8dfb81e13'}
for path,digest in expected.items():assert sha(P/path)==digest,path
m=read(P/'prepared_manifest.json');r=read(P/'prepared_receipt.json');cat=read(P/'catalog.json')
imports=read(P/'import_bindings.json');old=read(P/'closed_judge_bindings.json')
assert m['status']==r['status']=='PREPARED_SOURCE_ONLY_GATE_CLOSED' and not m['unresolved_modules'] and not imports['unresolved']
assert m['modules']==['GammaBoxBounds22','GammaContourComponent22'] and cat['total_declarations']==23 and cat['theorem_count']==17 and cat['definition_count']==6
assert len(m['immutable_inputs'])==6707 and len(old['inputs'])==209 and imports['module_count']==3235
assert {'Init','Init.Prelude'} <= {row['module'] for row in imports['entries']}
assert not m['author_olean_used'] and m['compiler_invocations']==m['numeric_invocations']==0
assert r['corrected_contour_not_compiled'] and not cat['corrected_contour_author_PASS_claimed']
assert m['readonly_local_dependencies']==['GammaPrerequisites22','GammaDerivative22']
for row in m['immutable_inputs']:assert sha(Path(row['path']))==row['sha256'],row['path']
for row in old['inputs']:assert sha(Path(row['path']))==row['sha256'],row['path']
for row in cat['modules']:assert sha(Path(row['source']))==sha(Path(row['original_source']))==row['source_sha256']
archive=read(B/'round22/previous_artifacts_sha256.json');assert archive['file_count']==len(archive['sha256'])==3089
for path,digest in archive['sha256'].items():assert sha(B/path)==digest,path
cpp=C/'checkpoint.json';cp=read(cpp);assert cp['official_auxiliary_validation']['modules']==66 and cp['official_auxiliary_validation']['declarations']==1109
assert not (P/'batch05_attempt01').exists()
gate={'schema':'ROUND22_JUDGE5_BATCH05_AUTHORIZATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'role':'ROLE5','authorized':True,'attempt':'batch05_attempt01','modules':m['modules'],'compiler_invocations_maximum':2,
 'source_manifest_sha256':expected['prepared_manifest.json'],'launcher_sha256':expected['run_once.py'],
 'preparation_receipt_sha256':expected['prepared_receipt.json'],
 'python_sha256':'4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c',
 'lean_sha256':'8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08',
 'readonly_local_dependencies':m['readonly_local_dependencies'],'independent_audit':True,'author_olean_allowed':False,'no_win':True,
 'source_FULL_ROOT_receipts':{'Box':'629aa7','corrected_Contour':'2d6dc7','launcher':'61ed7b','builder':'cb39a3','preparation':'dae070','catalog':'98a2f9','reads_and_prepared_receipt':'534216'},
 'large_JSON_scope':'Completely parsed and all bound bytes checked; no raw FULL display or mathematical import-closure audit',
 'inputs_verified':6707,'old_judge_files_verified':209,'archives_verified':3089,
 'root_compiler_invocations':0,'root_numeric_invocations':0,'H1_paid':False,'C5_paid':False,'D_N_paid':False,'WIN':False}
gp=C/'messages/round22_judge5_batch05_authorization.json'
with gp.open('x',encoding='utf-8') as f:json.dump(gate,f,ensure_ascii=False,indent=2);f.write('\n')
insight='New independent Judge batch05 Box12->correctedContour11 authorized by ROOT byte gate; two children maximum stopfirstFAIL, no old replay, only real Gamma/GammaPrime readonly dependencies. SOURCE23 and futureresult are not official; official66/1109 unchanged. Global numeric SOURCE review closed on paper, PREPARED launcher pending. H1/C3/C5/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
child=subprocess.run([sys.executable,'-B','-X','utf8',helper,'update','--cwd',str(B),'--run-name','parity','--node-id','15.3','--status','running','--insight',insight],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(gp.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==5:actor['status']='BATCH05_TWO_NEW_INDEPENDENT_CHILDREN_AUTHORIZED_NOT_STARTED'
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'gate':str(gp),'gate_sha256':sha(gp),'inputs':6707,'old_judge_files':209,'archives':3089,'compiler_invocations_ROOT':0},indent=2))
