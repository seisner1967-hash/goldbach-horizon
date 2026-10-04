"""Record a metadata binding failure without treating it as a math test."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';P=B/'round22/role4/h1_global_numeric/launch_prepare01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=read(P/'prepared_manifest22.json');r=read(P/'preparation22.json')
assert len(m['bindings'])==m['binding_count']==1 and len(r['bindings'])==r['binding_count']==2
assert m['source_packet_bindings']==14 and len(m['runtime_module_aliases'])==9
assert r['prepared_manifest_sha256']==sha(P/'prepared_manifest22.json')=='2cf83b5b923ec0da9b090e85ba4669fd0e5739c331e579ec25d98e6a44890024'
assert not (P/'actual_attempt01').exists() and not Path(r['root_gate_path']).exists()
assert m['new_math_invocations']==m['new_Lean_invocations']==0 and not m['WIN']
source_manifest=B/'round22/role4/h1_global_numeric/source_manifest22.json'
assert sha(source_manifest)==m['source_manifest_sha256']=='e1caa3d115dd492cfa6d91478240b0e8418614b6faf8798f48e15312dfe11a51'
source=read(source_manifest)
for row in source['bindings']:assert sha(Path(row['path']))==row['sha256'],row['path']
bindings={name:sha(P/name) for name in ['prepare_metadata_source22.ps1','run_global_once_source22.py','thermal_child_source22.py','launch_contract_source22.md','prepared_manifest22.json','preparation22.json']}
cpp=C/'checkpoint.json';cp=read(cpp);assert cp['official_auxiliary_validation']['modules']==68 and cp['official_auxiliary_validation']['declarations']==1132
o={'schema':'ROUND22_GLOBAL_PREPARATION01_METADATA_FAILURE_ROOT_OBSERVATION','time_utc':datetime.now(timezone.utc).isoformat(),
 'status':'INVALID_BINDING_METADATA_NO_NUMERIC_RUN','ROOT_FULL_prepared_JSON_read':'313370',
 'actual_manifest_binding_count':1,'actual_preparation_binding_count':2,'required_source_packet_binding_count':14,
 'actual_metadata_producer_command_receipt':'8b2946 exit0 (reported ROLE4; metadata only)',
 'cause_reported_ROLE4':'Sort-Object path -Unique reduced OrderedDictionary rows to a single path binding',
 'old_launch01_files_sha256':bindings,'source_packet_14_bindings_unchanged':True,
 'gate_created':False,'numeric_child_invocations':0,'mathematical_identity_tested':False,
 'repair_scope':'Separate launch_prepare02, explicit keyed deduplication and exact expected path-set guard; preserve01 bytes',
 'official_modules':68,'official_declarations':1132,'root_compiler_invocations':0,'root_numeric_invocations':0,
 'H1_paid':False,'D_N_paid':False,'WIN':False}
op=C/'messages/round22_global_prepare01_failure_observation.json'
with op.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Global numeric preparation01 metadata invalid:actual binding1/2 omits14source/9runtime closure dueSortObject path Unique; no gate/actual/numericchild/mathidentity tested. All14source bytes stable. Repairlaunch02 separate keyed map/exactpathset, preserves01. Official68/1132 incldefs; globalH1/C3/C5/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for cmd,args in [('record',['--node-id','15.3','--raw-report',insight,'--score','0','--insight',insight,'--result','METADATA_BINDING_FAILURE_NOT_NUMERICAL_OR_MATHEMATICAL_FAIL','--no-propagate']),('update',['--node-id','15.3','--status','running','--insight',insight])]:
 child=subprocess.run([sys.executable,'-B','-X','utf8',helper,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8');assert child.returncode==0,(child.stdout,child.stderr)
cp['phase']='ROUND22_GLOBAL_NUMERIC_PREPARATION01_INVALID_BINDINGS_REPAIR02'
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(op.relative_to(B)))
for actor in cp['in_flight_executors']:
 if actor['role']==4:actor['status']='NUMERIC_PREPARATION01_INVALID_BINDINGS_CLOSED_REPAIR02_DISTINCT'
 elif actor['role']==3:actor['status']='ROLE6_READY_NO_GATE_NO_ACTUAL_NUMERIC_CHILD'
 elif actor['role']==5:actor['status']='BATCH05_CLOSED_BATCH06_C5_CHAIN_SOURCE_PREPARATION'
cpp.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\nPréparation globale01 : échec METADATA constaté avant toute gate/calcul, manifest1binding/préparation2 au lieu de toutes14sources/9runtime et fermeture. Sort-Object path -Unique sur OrderedDictionary a réduit la liste ; les assertions de chiffres annoncés ne valent pas couverture des paths. Source14bytes stables, six fichiers01 conservés ; actual inexistant et aucun enfant numérique. Réparation02 distincte avec map parpath et égalité de set complet. Aucun FAIL identité/Goldbach/parité/Lean global ; officiel68/1132 inchangé et H1/D_N/WIN ouverts.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
