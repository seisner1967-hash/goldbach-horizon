"""Accept independent Judge verdict and byte conservation; no recompile/reproof."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/judge5'; A=P/'batch01_attempt01'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); m=read(P/'batch01_prepared_manifest.json'); d=read(P/'batch01_adjudication.json')
assert sha(P/'batch01_adjudication.json')=='43a3d84f51763ffd30c5a51ccf4bfb3c4307f3068d1b95aaa7afa1c9d2affba5'
assert sha(A/'receipt.json')==d['receipt_sha256']=='b41b67874e272165db455c0534aefbb4e8fb781d0309cd977e173c502a829dba'
assert sha(A/'PREEXEC.json')==d['PREEXEC_sha256'] and sha(A/'POSTEXEC.json')==d['POSTEXEC_sha256']
assert r['status']=='INDEPENDENT_BATCH01_AUX_PASS' and r['actual_child_invocations']==r['module_count_passed']==2 and r['declarations_passed']==51 and not r['victory'] and not r['author_olean_used']
assert pre['inputs']==post['inputs']==m['immutable_inputs'] and len(pre['inputs'])==7112 and post['all_inputs_unchanged'] and post['gate_unchanged']
for e in pre['inputs']: assert sha(Path(e['path']))==e['sha256'],e['path']
assert len(pre['captures'])==10
for e in pre['captures']: assert sha(Path(e['capture']))==e['sha256']==sha(Path(e['source']))
assert pre['protected_archives']==post['protected_archives'] and len(pre['protected_archives'])==3089
for e in pre['protected_archives']: assert sha(B/e['path'])==e['sha256']
assert not pre['author_olean_in_lean_path'] and sha(Path(pre['gate_path']))==pre['gate_sha256']==d['gate_sha256']
for row in r['rows']:
    assert row['exit_code']==0 and row['status']=='INDEPENDENT_LEAN_AUX_PASS' and row['exact_axiom_coverage_standard_only']
    assert sha(A/(row['module']+'.log'))==row['log_sha256'] and sha(A/(row['module']+'.olean'))==row['olean_sha256']
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':d['status'],'actual_independent_compiler_children':2,'copies_verified':10,'bindings_verified':7112,'archives_verified':3089,'adjudication_sha256':sha(P/'batch01_adjudication.json'),'receipt_sha256':sha(A/'receipt.json'),'root_FULL_reads':{'Kernel_log':'923f45','Finite_log':'c5b6f5','receipt':'7ae447','adjudication':'14402c','completion':'21e8bd'},'PRE_POST_scope':'Complete JSON parsed, structural equality and byte hashes checked; not FULL text display.','Judge_passed_declarations':51,'Judge_passed_theorems':42,'Judge_passed_definitions':9,'official_modules':59,'official_auxiliary_declarations':993,'count_includes_definitions':True,'author_PASS':2,'author_FAIL':8,'infinite_G0_credit':False,'Gamma_formal_credit':False,'global_continuous_contract_certified':False,'D_N_bound':False,'WIN':False,'root_compiler_invocations':0}
with (C/'messages/round22_judge_batch01_pass_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
insight='Independent Judge batch01 actual2children exit0,42theorems+9definitions,51standard prints;10captures/7112inputs/3089archives conserved. Official59modules/993auxiliarydeclarations, no globalWin. Unfold3technicalFAIL revision04 SOURCE pending; Gamma2 actual technical FAIL revision02 SOURCE pending; genuine G0/Γ banks closed,no replay.'
invoke('record','--node-id','16.1','--raw-report','# Running16.1 — independent Kernel/Finite certified\n\n'+insight+'\n','--score','0','--insight',insight,'--result','INDEPENDENT_KERNEL_FINITE_CERTIFIED_UNFOLD_SOURCE_GLOBAL_OPEN','--no-propagate')
invoke('update','--node-id','16.1','--status','running','--insight',insight)
root_insight='User definitive continuous pivot22: ban future arithmetic bilinear forms, combinatorial sieves, Mobius inversion, Vaughan and scalar AP remainders. Preserve fixed monograph/acquis/source logN>=1e24 and complete D_N ledger; N1e8 is finite bank. Official59modules/993auxiliarydeclarations after fresh independent Judge22 Kernel/Finite2modules51declarations; previous57/942 historical intact. All3089 prior protected artifacts conserved. New true G0 bank24cases and Gamma bank21cases AUX_PASS closed without replay; these do not certify Weil/heat/global coefficientN/D_N. Unfold3 technical Lean failures, revision04SOURCE pending; Gamma2 technical FAIL, revision02 SOURCE pending. ROOT coordinator only, no math/compiler. Real Weil H1, complete zero boxes/count/Stieltjes, genuine scattering/operator identification, global coefficient and D_N bridge remain OPEN. Continuous trace correlation allowed; relabeling convolution or defining answer into trace gives no victory. Active goal, no external blocker.'
invoke('update','--node-id','ROOT','--insight',root_insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_JUDGE_BATCH01_CERTIFIED_GAMMA2_AUTHOR_FAIL_UNFOLD4_SOURCE_GLOBAL_IDEATION'
cp['official_auxiliary_validation']={'modules':59,'declarations':993,'includes_definitions':True,'historical_modules':57,'historical_declarations':942,'new_modules':2,'new_declarations':51,'basis':'round22/judge5/batch01_adjudication.json','global_D_N_certified':False}
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_judge_batch01_pass_observation.json','round22/judge5/batch01_adjudication.json']
for actor in cp['in_flight_executors']:
    if actor['role']==5: actor['status']='BATCH01_CLOSED_INDEPENDENT_AUX_PASS_ACTOR_COMPLETE_NO_REPLAY'
    if actor['role']==4: actor['status']='GAMMA2_ACTUAL_TECHNICAL_FAIL_REVISION02_SOURCE_PENDING'
cp['in_flight_executors'].append({'role':1,'agent':'/root/round22_role1_trace_bridge','status':'GLOBAL_TRACE_BRIDGE_IDEATION_PAPER_SOURCE_ONLY'})
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nJuge22 batch01 réellement clos : deux enfants indépendants exit0,42théorèmes+9définitions/51audits standards,10captures/7112inputs/3089archives inchangés. Officiel59modules/993déclarations auxiliaires ; acquishistoriques57/942 conservés. Ce succès reste Kernel/Finite G0. Unfold etΓ non encore certifiés, trace globale/zéros/coefficientN/D_N ouverts, aucun WIN.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
