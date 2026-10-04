"""ROOT metadata progress only, with no mathematical evaluator or compiler."""
import hashlib,json,subprocess,sys
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
A=B/'round22/role4/h1_global_numeric/launch_prepare02/actual_attempt01'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
numeric_gate=C/'messages/round22_global_thermal_h1_authorization01.json'
judge_gate=C/'messages/round22_judge5_batch06_authorization.json'
assert sha(numeric_gate)=='e826200adca1e52b6362667a7c8e7ef7d80a1e75e4302d4c1163bf77dfe62b8d'
assert sha(judge_gate)=='f7ea9c8de7247c4ae931cae494344d9b98e457616af565dc2ed8437ed4992b0a'
start=read(A/'START.json');child=read(A/'child_START.json')
assert start['token']==child['token']=='c310745d96b943c99d7c9b85e1fb8d23'
assert start['PREEXEC_complete'] and start['max_children']==1 and start['no_retry']
assert start['context_sha256']==child['context_sha256']=='902ab13f6ca89da54ca6a5fe41a28896e32d32ea8894c9cfe687ee9d7521cf9b'
assert sha(A/'child_context.json')==start['context_sha256']
cp_path=C/'checkpoint.json';cp=read(cp_path)
assert cp['official_auxiliary_validation']['modules']==68 and cp['official_auxiliary_validation']['declarations']==1132
o=dict(schema='ROUND22_ROOT_DUAL_LAUNCH_METADATA_OBSERVATION',time_utc=datetime.now(timezone.utc).isoformat(),
 numeric_gate_sha256=sha(numeric_gate),judge_gate_sha256=sha(judge_gate),
 numeric_preparation_revision='launch_prepare02',invalid_preparation01_preserved=True,
 actual_numeric_controller_dispatch='5f24b4 session97614 (ROLE6)',
 actual_numeric_START=start['time_utc'],actual_numeric_child_START=child['time_utc'],
 start_sha256=sha(A/'START.json'),child_START_sha256=sha(A/'child_START.json'),
 ROOT_FULL_actual_START_read='d67e62',context_sha256=start['context_sha256'],
 numeric_evaluation_level='PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER',
 structural_PASS_is_enclosure_PASS=False,numeric_result_certified=False,
 judge_batch06='AUTHORIZED_NINE_NEW_AUXILIARY_CHILDREN_STOP_FIRST_FAILURE',
 source_C5_count=88,official_modules=68,official_declarations=1132,
 ROOT_numeric_invocations=0,ROOT_Lean_invocations=0,H1_formal='OPEN',C5_global='OPEN',D_N='UNPAID',WIN=False)
path=C/'messages/round22_dual_launch_observation.json'
with path.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
insight='Continuous pivot: separate metadata revision02 closed1003bindings14sources9aliases972runtime; ROOT numeric gate verified3089archives. Actual ROLE6 global child START13:03:11UTC, fixedN1e8 Y1e4,217088nodes and999999integers pending,3600s/2GiB1child/no retry. Judge batch06 nine C5 SOURCE88 authorized separately, max9children stopfirstFAIL; no PASS credited. Formalizer4 pays Mellin->Arch SOURCE. Official68/1132 unchanged; H1/C5global/additiveN/D_N/WIN open.'
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
result=subprocess.run([sys.executable,'-B','-X','utf8',helper,'update','--cwd',str(B),'--run-name','parity','--node-id','15.3','--status','running','--insight',insight],capture_output=True,text=True,encoding='utf-8')
assert result.returncode==0,(result.stdout,result.stderr)
cp['phase']='ROUND22_GLOBAL_NUMERIC_ACTUAL_RUNNING_AND_C5_BATCH06_AUTHORIZED'
cp['last_progress']=insight
cp['previous_goal_turn_evidence'].extend([str(path.relative_to(B)),str(numeric_gate.relative_to(B)),str(judge_gate.relative_to(B))])
for actor in cp['in_flight_executors']:
 if actor['role']==3:actor['status']='ROLE6_GLOBAL_NUMERIC_ACTUAL_RUNNING_ONE_CHILD_NO_RETRY'
 elif actor['role']==4:actor['status']='GLOBAL_C5_MELLIN_ARCH_SOURCE_CONTINUATION'
 elif actor['role']==5:actor['status']='BATCH06_NINE_NEW_AUXILIARY_CHILDREN_AUTHORIZED'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:
 f.write('\nLa préparation distincte02 corrige le défaut metadata01 : 1003 fichiers hashés, 14 sources, 9 alias, 972 runtime ; les six anciens01 restent conservés. ROOT gate numérique créée c19adc, lancement réel unique ROLE6 5f24b4/session97614 ; START enfant 2026-10-03 13:03:11UTC. Paramètres N=10^8,Y=10000,T=100,X=Q=R=10^6 fixés, limites3600s/2Gio, no retry ; aucune garde ni identité globale validée à ce stade. Revue primitives/restes au niveau papier et checker structurel restent distincts. ROOT gate batch06 C5 créée a13cb2 pour neuf sources88 déclarations, au plus9 enfants arrêt premierFAIL. Officiel68/1132 inchangé. SOURCE Mellin vers Arch se poursuit ; H1/C5global/coefficientN/D_N/WIN ouverts.\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
