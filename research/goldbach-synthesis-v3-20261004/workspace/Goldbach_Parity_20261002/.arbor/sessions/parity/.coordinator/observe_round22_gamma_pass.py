"""Observe producer verdicts and all captured bytes; no mathematical replay/audit."""
import json, hashlib, subprocess, sys
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; A=B/'round22/role6/gamma_h2/actual_gamma22'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
receipt=read(A/'actual_receipt.json'); result=read(A/'gamma_result22.json'); post=read(A/'POSTEXEC_integrity.json'); captures=read(A/'PREEXEC_captures.json')
assert receipt['exit_code']==0 and receipt['post_integrity'] and post['all_unchanged'] and not receipt['WIN']
hashes={'result':sha(A/'gamma_result22.json'),'log':sha(A/'actual.log'),'certificates':sha(A/'gamma_sqrt_certificates22.jsonl'),'receipt':sha(A/'actual_receipt.json'),'PREEXEC':sha(A/'PREEXEC_captures.json'),'POSTEXEC':sha(A/'POSTEXEC_integrity.json')}
assert hashes['result']==receipt['result_sha256']=='595b15340efe03bd215eebe7f6d526cd1f2f5d07865f074a3b7927687beb967a'
assert hashes['log']==receipt['log_sha256']=='8c0e2febec17d75b95c73e6aef85fdb67c6322b3049ebb5473c4b9c94bdacbd5'
assert hashes['certificates']==receipt['sqrt_certificate_sha256']=='c1ad2c55609947d95cfdb779b5c808ac334b0c77c5cc72f11f2891d17438077e'
assert len(captures['captures'])==17
for e in captures['captures']: assert sha(Path(e['copy']))==e['sha256']==sha(Path(e['source']))
for e in post['bindings']: assert e['unchanged'] and sha(Path(e['path']))==e['expected_sha256']==e['actual_sha256']
assert result['status']==result['verdict']=='GAMMA_ROTATED_LAPLACE_AUX_PASS' and result['cases_evaluated']==len(result['cases'])==21
assert result['mutation_applicable']==result['mutation_detected']==12
assert result['primitive_counters']=={'exp':38981,'sin_cos':68117,'sqrt':43,'pi':1}
assert len(result['noninformative_zero_mutant_cases'])==6 and not result['WIN'] and not result['D_N_claim']
rows=[]
for r in result['cases']:
    assert r['status']=='GAMMA_AUX_CASE_PASS' and r['target_intersects'] and r['absolute_tolerance_met'] and r['arithmetic_cap_met'] and r['H2_sample_upper_at_most_two']
    rows.append({k:r[k] for k in ['sigma','gamma','status','target_intersects','absolute_tolerance_met','arithmetic_cap_met','H2_sample_upper_at_most_two','max_distance','arithmetic_component_width','zero_mutant_not_discriminated_at_this_tolerance']})
    rows[-1]['mutant_applicable']=r['omitted_attenuation_mutant']['applicable']; rows[-1]['mutant_detected']=r['omitted_attenuation_mutant'].get('detected')
obs={'created_utc':datetime.now(timezone.utc).isoformat(),'scope':'PRODUCER_OUTPUT_STATUS_AND_METADATA_PROJECTION_NO_MATHEMATICAL_REPLAY','status':result['status'],'actual_attempts':1,'started':receipt['actual_START'],'finished':receipt['actual_FINISH'],'exit_code':0,'token':receipt['attempt_token'],'hashes':hashes,'copies_verified':17,'postbindings_verified':15,'full_root_receipt':'633b30','full_root_log':'0e7f4b','full_root_POST':'704714','full_root_PRE':'ce0775','result_FULL_text_displayed':False,'result_scope':'Complete JSON parsed; complete21case status/distance/width projection,244209rawbytes preserved/SHA verified; numerical rectangles not all displayed.','certificates_scope':'43producer-counted square certificates with source integer checks; fileSHA verified, no independent root square recomputation.','analytic_radius':result['analytic_radius'],'primitive_counters':result['primitive_counters'],'cases':rows,'noninformative_zero_mutants':6,'N_metadata_only':True,'Weil_evaluations':0,'heat_evaluations':0,'coefficient_N_evaluations':0,'Lean_evaluations':0,'D_N_claim':False,'WIN':False,'root_math_invocations':0,'period_width_note_FULL':'d6c16d','next':'Genuine Gamma Lean first author compilation can receive separate frozen source gate; no fulltrace/global credit.'}
with (C/'messages/round22_gamma_pass_observation.json').open('x',encoding='utf-8') as f: json.dump(obs,f,ensure_ascii=False,indent=2); f.write('\n')
H=r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
insight='New Gamma unique actual07:28:40..07:34:55UTC exit0,21cases AUX_PASS,12mutants detected,43sqrtcertificates,15bindings/17copies unchanged. Complete case-status projection and sourceFULL; raw244209byte result bound, not falsely FULL displayed. Sixgamma±100zero-mutants noninformative. GenuineGamma firstLean pending; trueWeil/zeroCount/heat/coefficientN/D_N OPEN,noWin.'
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',H,cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8'); assert p.returncode==0,(p.stdout,p.stderr)
invoke('record','--node-id','15.2','--raw-report','# Running15.2 — genuine Gamma numerical auxiliary PASS\n\n'+insight+'\n','--score','0','--insight',insight,'--result','ACTUAL_GAMMA_NUMERIC_AUX_PASS_FORMAL_PENDING_GLOBAL_TRACE_OPEN','--no-propagate')
invoke('update','--node-id','15.2','--status','running','--insight',insight)
cp=read(C/'checkpoint.json'); cp['phase']='ROUND22_GAMMA_ACTUAL_AUX_PASS_FIRST_GAMMA_LEAN_PENDING_FINITE_AUTHOR_RUNNING'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round22_gamma_pass_observation.json','round22/role6/gamma_h2/actual_gamma22/actual_receipt.json']
for actor in cp['in_flight_executors']:
    if actor['role']==6: actor['status']='GAMMA_UNIQUE_ACTUAL_AUX_PASS_CLOSED_NO_REPLAY'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f: f.write('\nBancΓ22 réel : unique essai07:28:40..07:34:55UTC exit0,21cas AUX_PASS et12mutations détectées,43certificats racine,17captures/15bindings inchangés. Les6cas hauteur±100 ne discriminent pas un mutant zéro à la tolérance absolue. Aucun crédit Lean, formuleWeil, chaleur, coefficientN ouD_N sur ce test.\n')
print(json.dumps(obs,ensure_ascii=False,indent=2))
