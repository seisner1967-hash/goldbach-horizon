"""Resume bookkeeping only; no compiler, numeric evaluation or source edits."""
import hashlib,json,subprocess,sys
from datetime import datetime,timezone
from pathlib import Path
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
cp_path=C/'checkpoint.json';cp=read(cp_path);tree=read(C/'idea_tree.json')
assert cp['official_auxiliary_validation']['modules']==78 and cp['official_auxiliary_validation']['declarations']==1304
last=read(C/'messages/round22_native_contract_final_observation.json')
for x in last['entries']:assert sha(B/x['path'])==x['sha256'],x['path']
helper=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def change(command,extra):
 r=subprocess.run([sys.executable,'-B','-X','utf8',helper,command,'--cwd',str(B),'--run-name','parity',*extra],capture_output=True,text=True,encoding='utf-8');assert r.returncode==0,(r.stdout,r.stderr)
requeued=[]
for name in ['15.2','16.1','15.3']:
 if tree['nodes'][name]['status']=='running':change('update',['--node-id',name,'--status','pending']);requeued.append(name)
insight='Reprise utilisateur continue: officiel78modules1304declarations auxiliaires, identites thermiques11/13/15 et precision/enveloppe17 compilees. SOURCE GammaMellin11 prepare pour Judge18 sans recompile anciens; BUILD03 revise le perimetre de confiance statique Windows/GCC sans faux loaderglobal et sans execution des .exe. SOURCE projection corpsfini en parallele, compiler gate et bankN1e8 distincts; D_N/WIN ouverts.'
change('update',['--node-id','ROOT','--insight',insight])
change('update',['--node-id','15.3','--status','running','--insight',insight])
# Disable the stale monolithic evaluator; every actual run has its exact gate.
change('meta',['--set','eval_cmd=null','--set','eval_cmd_test=null','--set','dataset_info=ROUND22 continuous pivot resumed; metricWIN0, official78/1304 auxiliary proofs; all actual commands require per-attempt independent manifests and ROOT gates, no inherited monolithic evaluator; fullcoefficient/D_N open.'])
o=dict(schema='ROUND22_ROOT_RESUME_CONTINUE03',utc=datetime.now(timezone.utc).isoformat(),source_instruction='human continue',initial_official_modules=78,initial_official_declarations=1304,old_final_bound_entries_verified=len(last['entries']),requeued_nodes=requeued,selected_node='15.3',initialization_restarted=False,stale_monolithic_eval_disabled=True,new_Lean_invocations=0,new_numeric_invocations=0,previous_truncated_CP_read='3d5231 excluded as FULL; selected fields parsed300f01',FULL_constraints='3486e3',FULL_skills='61f119/22eaaf',goal_status_not_changed=True,D_N_paid=False,WIN=False)
out=C/'messages/round22_resume_continue03.json'
with out.open('x',encoding='utf-8') as f:json.dump(o,f,ensure_ascii=False,indent=2);f.write('\n')
cp['phase']='ROUND22_RESUMED_GAMMA18_SOURCE_FINITE_FIELD_AND_BUILD03_PREPARING'
cp['last_progress']=insight;cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
cp['in_flight_executors']=[dict(role=3,agent='/root/round22_formal3_prepare',status='SOURCE_FINITE_FIELD_AND_ROLE6_BUILD03_METADATA_ACTIVE'),dict(role=4,agent='/root/round22_formal4_trace',status='BUILD03_SOURCE_TRUST_SCOPE_REVISION_ACTIVE'),dict(role=5,agent='/root/round22_judge5_independent',status='GAMMA_MELLIN_BATCH18_METADATA_PREPARING_NO_COMPILE')]
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:f.write('\n'+insight+'\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
