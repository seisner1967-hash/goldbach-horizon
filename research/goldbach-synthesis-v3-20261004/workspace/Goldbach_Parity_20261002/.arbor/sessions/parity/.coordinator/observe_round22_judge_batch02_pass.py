"""Record real Judge findings and conservation; no independent math or compiler."""
import argparse, json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; P=B/'round22/judge5'; A=P/'batch02_attempt01'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser(); parser.add_argument('--adjudication-sha',required=True); parser.add_argument('--adjudication-read',required=True); parser.add_argument('--completion-read',required=True); args=parser.parse_args()
r=read(A/'receipt.json'); pre=read(A/'PREEXEC.json'); post=read(A/'POSTEXEC.json'); m=read(P/'batch02_prepared_manifest.json'); d=read(P/'batch02_adjudication.json')
assert sha(P/'batch02_adjudication.json')==args.adjudication_sha
assert sha(A/'receipt.json')=='a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9'
assert sha(A/'PREEXEC.json')=='0c553b9634a2bcb260af455cdf777f0f16e44b546fb6bee7723b7cc1c0be2ec0'
assert sha(A/'POSTEXEC.json')=='2d419ab806681df15e55bd9a876548a32c9308577fa0ecded961c3775c15153d'
assert r['status']=='INDEPENDENT_BATCH02_AUX_PASS' and r['actual_child_invocations']==r['module_count_passed']==3 and r['declarations_passed']==56
assert not r['victory'] and not r['author_olean_used'] and not r['batch01_recompiled'] and not r['hidden_retries']
assert pre['inputs']==post['inputs']==m['immutable_inputs'] and len(pre['inputs'])==7214
assert post['all_inputs_unchanged'] and post['gate_unchanged']
for row in pre['inputs']: assert sha(Path(row['path']))==row['sha256'],row['path']
assert len(pre['captures'])==23
for row in pre['captures']: assert sha(Path(row['capture']))==row['sha256']==sha(Path(row['source']))
assert pre['protected_archives']==post['protected_archives'] and len(pre['protected_archives'])==3089
for row in pre['protected_archives']: assert sha(B/row['path'])==row['sha256']
assert not pre['author_olean_in_lean_path']
assert sha(Path(pre['gate_path']))==pre['gate_sha256']=='6c6aaf32ebc56e6f445073b874db729c1ff728d9e3533cae0390f510fd47d51d'
for row in r['rows']:
    assert row['exit_code']==0 and row['status']=='INDEPENDENT_LEAN_AUX_PASS' and row['exact_axiom_coverage_standard_only']
    assert sha(A/(row['module']+'.log'))==row['log_sha256'] and sha(A/(row['module']+'.olean'))==row['olean_sha256']
oldbindings=read(P/'batch02_batch01_bindings.json'); assert len(oldbindings['inputs'])==35
for row in oldbindings['inputs']: assert sha(Path(row['path']))==row['sha256']
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'status':r['status'],'actual_independent_compiler_children':3,'copies_verified':23,'bindings_verified':7214,'archives_verified':3089,'readonly_batch01_files_verified':35,'adjudication_sha256':sha(P/'batch02_adjudication.json'),'receipt_sha256':sha(A/'receipt.json'),'root_FULL_reads':{'Unfold_log':'8fc327','Tail_log':'c83cda','Gamma_log':'819836','receipt':'5ee76b','adjudication':args.adjudication_read,'completion':args.completion_read},'PRE_POST_scope':'Complete JSON parsed, structural equality and byte hashes checked; not FULL text display.','new_passed_declarations':56,'new_passed_theorems':47,'new_passed_definitions':9,'official_modules':62,'official_auxiliary_declarations':1049,'count_includes_definitions':True,'author_PASS':5,'author_technical_FAIL':8,'Judge22_actual_PASS_modules':5,'Judge22_actual_FAIL_modules':0,'genuine_G0_unfolding_and_actual_error_certified':True,'genuine_Gamma_H2_certified':True,'H1_global_trace_certified':False,'global_coefficient_N_certified':False,'D_N_bound':False,'WIN':False,'root_compiler_invocations':0,'root_numeric_invocations':0}
with (C/'messages/round22_judge_batch02_pass_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(cmd,*items):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*items],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
g0='Real independent Judge22 G0 four modules complete: Kernel/Finite previously closed, Unfold/Tail new actual2children exit0; genuine infinite unfolding and actual positive truncation error/joint continuous envelope certified. No scattering/operator/global coefficient/D_N credit. Old G0 bank24cases closed, no replay.'
gamma='Real independent Judge22 Gamma H2 actual exit0,23standard prints; genuine complex Laplace identity and exponential Gamma bound certified. Gamma-prime/boxes/extended-strip sources uncompiled; true H1/Weil/zero completeness/global coefficient/D_N open. Old Gamma21cases bank closed, no replay.'
for node,insight,result in [('16.1',g0,'G0_ANALYTIC_UNFOLD_AND_ACTUAL_ERROR_CERTIFIED_GLOBAL_OPEN'),('15.2',gamma,'GAMMA_H2_CERTIFIED_H1_AND_GLOBAL_OPEN')]:
    invoke('record','--node-id',node,'--raw-report','# Independent auxiliary result\n\n'+insight+'\n','--score','0','--insight',insight,'--result',result,'--no-propagate')
    invoke('update','--node-id',node,'--status','running','--insight',insight)
insight='Definitive pivot22 maintained: no future arithmetic bilinear/sieve/Mobius/Vaughan/AP remainder methods. Fixed acquis and full D_N ledger/source logN>=1e24 unchanged. Official62modules/1049auxiliarydeclarations after5real independent Judge22 PASS modules/107declarations, no JudgeFAIL. Authors5PASS8technicalFAIL retained. G0 analytic unfolding/actual truncation error and Gamma H2 certified; numerical banks G0/Gamma closed without replay. New H1 contour15.3 paper precritique/source Euler/Mellin/FE/psi work active; its global identity/numerical enclosure/finite zero residue/whole coefficientN/D_N unpaid, NO WIN. ROOT coordinator only, no math/compiler.'
invoke('update','--node-id','ROOT','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_GAMMA_INDEPENDENT_CERTIFIED_H1_15_3_SOURCE_NUMERIC_PREPARATION'
cp['official_auxiliary_validation']={'modules':62,'declarations':1049,'includes_definitions':True,'historical_modules':57,'historical_declarations':942,'new_modules':5,'new_declarations':107,'basis':'round22/judge5/batch02_adjudication.json','global_D_N_certified':False}
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_judge_batch02_pass_observation.json','round22/judge5/batch02_adjudication.json']
for actor in cp['in_flight_executors']:
    if actor['role']==5: actor['status']='BATCH02_CLOSED_AUX_PASS_H1_INDEPENDENT_SOURCE_REVIEW_NO_COMPILATION'
    if actor['role']==4: actor['status']='GAMMA_H2_INDEPENDENT_CERTIFIED_H1_EULER_PSI_SOURCE_ACTIVE'
    if actor['role']==6: actor['status']='H1_15_3_PAPER_PRECRITIQUE_COMPLETE_EVALUATOR_SOURCE_PREPARATION_ONLY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nJuge22 batch02 clos : trois vrais enfants indépendants exit0,47théorèmes+9définitions/56audits standards,23captures/7214inputs/3089archives et35fichiers batch01 inchangés. Officiel62modules/1049déclarations auxiliaires. Le dépliement G0, sa vraie erreur et Γ/H2 sont certifiés ; H1/trace globale, certificat numérique contour, coefficientN et D_N restent ouverts. Aucun WIN.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
