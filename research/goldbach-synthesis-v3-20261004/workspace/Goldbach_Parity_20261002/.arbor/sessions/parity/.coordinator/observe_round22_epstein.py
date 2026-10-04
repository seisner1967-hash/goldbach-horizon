"""Read archived outputs and hashes; no evaluator/compiler or numeric replay."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round22'; C=B/'.arbor/sessions/parity/.coordinator'; A=R/'role6/actual_epstein22'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
receipt=read(A/'actual_receipt.json'); result=read(A/'epstein_result22.json'); start=read(A/'actual_START.json'); caps=read(A/'PREEXEC_captures.json'); post=read(A/'POSTEXEC_integrity.json')
assert receipt['exit_code']==0 and receipt['launch_error'] is None and receipt['post_integrity']
assert result['status']=='EPSTEIN_UNFOLDING_AUX_PASS' and result['scope']=='EPSTEIN_UNFOLDING_AUX_ONLY'
assert result['actual_cases']==len(result['cases'])==24 and result['integer_square_certificates']==295198
assert all(x['target_intersects'] and x['tolerance_satisfied'] and x['tail_cap_satisfied'] for x in result['cases'])
assert len([x for x in result['cases'] if x['finite_two_routes_intersect'] is True])==18
assert len([x for x in result['cases'] if x['mutation_factor_abs_m_detected'] is True])==16
assert len([x for x in result['cases'] if x['mutation_factor_abs_m_detected'] is None])==8
assert not result['Lean_compiled'] and not result['D_N_bound_proved'] and not result['coefficient_N_computed'] and not result['heat_signal_computed'] and not result['Weil_trace_computed']
assert receipt['attempt_token']==caps['attempt_token']==start['attempt_token']=='5737a2bd29dd4cd7a8851212a692e7c3'
assert len(caps['captures'])==23 and start['captures_complete'] and not caps['math_started']
for row in caps['captures']: assert row['phase']=='PREEXEC' and sha(Path(row['copy']))==row['sha256']
assert post['all_unchanged'] and post['preparation_unchanged'] and post['gate_unchanged']
assert len(post['bindings'])==21
for row in post['bindings']: assert row['unchanged'] and sha(Path(row['path']))==row['expected_sha256']==row['actual_sha256']
for filename,key in [('actual.log','log_sha256'),('epstein_result22.json','result_sha256'),('epstein_sqrt_certificates22.jsonl','sqrt_certificate_sha256')]: assert sha(A/filename)==receipt[key]
assert (A/'epstein_sqrt_certificates22.jsonl').stat().st_size==101630615
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'scope':'ARCHIVED_OUTPUT_AND_BYTE_METADATA_OBSERVATION_NOT_EVALUATION','actual_actor':'ROLE6','actual_attempts':1,'actual_START':receipt['actual_START'],'actual_FINISH':receipt['actual_FINISH'],'actual_exit_code':0,'status':result['status'],'root_FULL_result':['115c5c lines1..750','d0c146 lines751..1244'],'root_FULL_START_PREEXEC':'d2f1e2','root_FULL_POSTEXEC_LOG':'ab9df4','root_FULL_receipt':'1fe4f7','case_count':24,'finite_routes_agree':18,'mutant_q_detected':16,'mutant_q_not_applicable':8,'square_certificates_declared':295198,'square_certificates_file_bytes':101630615,'square_certificates_scope':'SHA256 bound, not FULL101MB individual verification by coordinator','captures_verified':23,'bindings_verified':21,'hashes':{'result':sha(A/'epstein_result22.json'),'receipt':sha(A/'actual_receipt.json'),'log':sha(A/'actual.log'),'sqrt_certificates':sha(A/'epstein_sqrt_certificates22.jsonl'),'PREEXEC':sha(A/'PREEXEC_captures.json'),'POSTEXEC':sha(A/'POSTEXEC_integrity.json')},'root_math_invocations':0,'Lean22_invocations':0,'official_modules':57,'official_auxiliary_theorems':942,'win':False,'remaining':'G0 Lean sources/compiler/Judge not yet certified; Gamma/Weil/HEAT/coefficientN/D_N separate OPEN obligations.'}
(C/'messages/round22_epstein_observation.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
def invoke(*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,'update','--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('--node-id','16.1','--status','running','--insight','Actual unique ROLE6 G0 bank24cases PASS06:49:45..06:49:54UTC exit0;18finite routes and16applicable qmutants,295198squarecertificates. Root FULL outputs/SHA/PREEXEC23/POST21 verified, no old replay. Author Lean/compiler/Judge gate still closed awaiting FINALsources/builder/prep. Primitive/row/infinite/tail not yet kernel-certified; heat, scattering, coefficientN andD_N OPEN. NoWin.')
tree=read(C/'idea_tree.json'); old=tree['nodes']['ROOT']['insight']; needle='Aucun math22/Lean22/PASS22 exécuté ou autorisé.'
assert needle in old
invoke('--node-id','ROOT','--insight',old.replace(needle,'Un unique banc ROLE6 Epstein24cas a réellement passé, avec gardes sources fausses, sources intactes et certificat dyadique ; aucun Lean22 encore exécuté ou autorisé. Le succès numérique AUX ne paie ni chaleur, vraie diffusion, coefficientN niD_N.'))
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_G0_ACTUAL_AUX_PASS_FORMAL_SOURCES_PENDING_GAMMA_SOURCE_PREPARATION'; cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_epstein_observation.json','round22/role6/actual_epstein22/actual_receipt.json','round22/role6/actual_epstein22/epstein_result22.json']
for actor in cp['in_flight_executors']:
    if actor['role']==6: actor['status']='G0_UNIQUE_AUX_PASS_GAMMA_SOURCE_ONLY_NEXT'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
report=B/'REPORT.md'; body=report.read_text(encoding='utf-8'); needle2='Aucun banc ou module22 n\'a encore été exécuté ou validé.'
assert body.count(needle2)==1
body=body.replace(needle2,'Le banc géométrique unique du rôle6 a terminé à06:49:54UTC avec exit0 :24cas compatibles dans la tolérance1/100000,18comparaisons de fenêtres et16mutations du facteurq détectées ;295198certificats carrés sont archivés. Ce résultat est EPSTEIN_UNFOLDING_AUX_PASS. Aucun module22 n\'a encore été compilé ou certifié par le Juge. Il ne calcule ni le signal de chaleur, ni le coefficientN, ni D_N.')
report.write_text(body,encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
