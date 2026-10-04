"""Coordinator byte and stored receipt observations only; no mathematics/Lean."""
import hashlib,json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round20'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
bindings={}
def bind(path,digest):
    p=Path(path)
    if not p.is_absolute():p=B/p
    key=str(p)
    assert key not in bindings or bindings[key]==digest,key
    bindings[key]=digest
def bindmap(d):
    for p,h in d.items():bind(p,h)
fixed={
 'role3/final_receipt.json':'fd8dbf9541748392ba0f3fe3f925cef859ee92407760329dbad82ae166763654',
 'role3/final_manifest.json':'9d1986139716428392958d99cc57b3bd810356b9a082d1be854174fe3a2e2c53',
 'agent3_formalisation.md':'43363b11060a822b75f52c8753c4ad33d41bd3de2a20620a4e1bfb9074ba7e02',
 'role4/final_receipt.json':'23f579a279b9acf2f0dfd19b8761c54c1753ad231de1808d0fea206479236df8',
 'role4/output_manifest.json':'f5382d4616a772b82e39bbf3c1d486261db8798840aa364d1afb3d4305e81cff',
 'agent4_formalisation.md':'173a45bb5a4e3c9e247d811cec34185ef4fbde2ca98888b99a355fb87e8562ea',
 'role12_feedback/final_receipt.json':'6a2281269fca41a4b70cd0dbb90d4c53fded1f40b6dc4918d5ed85e7c9579356',
 'role12_feedback/final_manifest.json':'9a69fa4336c36cf0af2fd4d5621bb957bc37996b8d1978508d504adb87cee06f',
 'ideation_failure_feedback20_final.md':'c75c62b86ed6b7352d3a77a86d578171fbd73920f72711d6ac4eb74e503aa444',
 'role3/build_receipt.json':'94a0badf1d1e22ff21c4c60dde8b2d0cdbda615b8e0e755ceca08be9512c0aa3',
 'role6/final_manifest.json':'25ddedcbf52dff612595770a671de3129d9e29e7da84212983094e6fe98baa5e',
 'role6/final_receipt.json':'5e74e0a1839c746fc828e0be09050d57f6f09ae33a115c5fa91dc13ea461a5e5'}
for p,h in fixed.items():
    assert sha(R/p)==h,p
    bind(R/p,h)
f3=load(R/'role3/final_receipt.json');m3=load(R/'role3/final_manifest.json')
assert f3['actual_lean_invocations']==14 and f3['actual_new_PASS']==6 and f3['actual_lean_failures']==8
assert f3['totals']=={'modules':6,'definitions':50,'theorems':91,'printed_axioms':141}
assert not f3['victory'] and not f3['parity_bypass_proved'] and not f3['whole_D_N_bound_proved']
for key in ['owned_artifacts_sha256','historical_dependencies_sha256','canonical_bank_bindings_sha256','original_documents_sha256']:
    bindmap(m3[key])
f4=load(R/'role4/final_receipt.json');m4=load(R/'role4/output_manifest.json')
assert f4['logical_ROLE4_total_Lean_invocations']==24 and f4['logical_ROLE4_total_PASS']==10
assert f4['logical_ROLE4_total_FAIL']==14 and f4['public_axiom_prints_checked']==193
assert not f4['victory'] and not f4['whole_ledger_paid'] and not f4['independent_Judge20_executed']
for key in ['owned_files','external_geometry_readonly']:
    for x in m4[key]:bind(x['path'],x['sha256'])
assert len(m4['owned_files'])==185
for key in ['report','final4','manifest','compiler_failures','read_input_sha256','read_input_sha256_v2']:
    bind(f4[key]['path'],f4[key]['sha256'])
feedback=load(R/'role12_feedback/final_manifest.json');fr=load(R/'role12_feedback/final_receipt.json')
assert len(feedback['bindings'])==fr['final_binding_count']==75
assert fr['role3_cutoff_attempt']==14 and not fr['victory']
bindmap(feedback['bindings'])
numeric=load(R/'role6/final_manifest.json')
assert len(numeric['sha256'])==677
bindmap(numeric['sha256'])
ledger=load(R/'role3/build_receipt.json'); attempts=ledger['attempts']
assert len(attempts)==14
assert [x['actual_exit_code'] for x in attempts]==[1,0,1,0,1,0,1,1,0,1,0,1,1,0]
actual=[]
for a in attempts:
    assert all(a[k] for k in ['source_unchanged','readonly_dependencies_unchanged','runtime_unchanged','authorization_unchanged','canonical_numeric_bank_unchanged'])
    assert all(a[k]==0 for k in ['old_rebuilds','old_PASS_replays','numeric_invocations','judge_invocations'])
    for k,h in [('source_capture','source_capture_sha256'),('launcher_capture','launcher_sha256'),('authorization_capture','authorization_sha256'),('log_path','log_sha256')]:bind(a[k],a[h])
    start=R/'role3'/('attempt%02d_%s_started.json'%(a['attempt'],a['module']))
    s=load(start)
    assert s['started_utc']==a['started_utc'] and s['actual_command']==a['actual_command']
    assert s['source_sha256']==a['source_sha256'] and s['source_capture']==a['source_capture']
    assert s['launcher_sha256']==a['launcher_sha256'] and s['authorization_sha256']==a['authorization_sha256']
    bind(start,sha(start))
    for key in ['checked_inputs_sha256','readonly_dependencies_sha256','runtime_readonly_sha256']:bindmap(a[key])
    if a['actual_exit_code']==0:
        bind(a['source_path'],a['source_sha256'])
        bind(a['olean_path'],a['olean_sha256'])
        bind(a['olean_capture'],a['olean_capture_sha256'])
    actual.append({k:a[k] for k in ['attempt','module','started_utc','finished_utc','actual_exit_code','status','source_sha256','source_capture','log_path','log_sha256']})
for path,digest in bindings.items():assert sha(path)==digest,path
observation={'round':20,'observed_at_utc':datetime.now(timezone.utc).isoformat(),
 'status':'ALL_AUTHOR_FINALS_FROZEN_BYTE_VERIFIED_JUDGE_PREPARATION_ONLY',
 'fixed_final_hashes':fixed,'checked_bindings':bindings,'binding_count':len(bindings),
 'actual_role3_attempts':actual,'role3_author_modules':6,'role4_author_modules_including_geometry':10,
 'actual_author_Lean_invocations':38,'actual_author_unique_PASS_modules':16,'actual_author_technical_FAIL':22,
 'root_FULL_final3_report_and_receipt':'c7f906','root_FULL_final4_report':'edb590','root_FULL_final4_receipt':'db017d',
 'root_FULL_final4_read_v2_and_failure_journal':'8bac8b','root_FULL_conceptual_feedback':'185054',
 'root_FULL_role3_current_sources':['2ac3b3 (LeastFactor only)','6dac43','33b51c','a8a66a'],
 'root_FULL_role3_logs_01_07':['76935d','b33c78'],'root_FULL_role3_logs_08_14':['137f34','33b51c','dcf75c'],
 'all_numeric_FINAL677_bindings_reverified_only':True,'independent_Judge20_executed':False,
 'cumulative_official_modules_until_Judge20':41,'cumulative_official_theorems_until_Judge20':692,
 'root_mathematical_executions':0,'root_Lean_executions':0,'sign_or_log_recomputations':0,
 'source_bridge_proved':False,'B6_SD_paid':False,'F0_minus_F1_nonfriable_reciprocal_paid':False,
 'whole_DN_bound_proved':False,'victory':False}
out=C/'messages/round20_author_finals_root_observation.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(observation,f,ensure_ascii=False,indent=2);f.write('\n')
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_ALL_AUTHOR_FINALS_FROZEN_ROOT_VERIFIED_INDEPENDENT_JUDGE_PREPARATION'
for e in cp['in_flight_executors']:
    if e['role']==3:e['status']='FINAL3_SIX_UNIQUE_PASS_14_ACTUALS_8_TECHNICAL_FAIL_ROOT_BYTE_VERIFIED'
    if e['role']==4:e['status']='FINAL4_TEN_MODULES_INCLUDING_GEOMETRY_24_ACTUALS_14_TECHNICAL_FAIL_ROOT_BYTE_VERIFIED'
cp['in_flight_executors'].append({'role':5,'agent':'/root/round20_lean_judge','ownership':['round20/judge/**','round20/agent5_judge.md','round20/adjudication.json'],'status':'PREPARATION_ONLY_NO_COMPILE_GATE_YET'})
cp['last_progress']+=' FINAL3/4+feedbackFULL/rootbytes frozen;38authoractuals16uniquePASS22techFAIL;Judge20 preparing freshcopies excludesallauthor20oleans, no runtime/oldmathreplay. Official41/692 remains until independentJudge; noDN/Win.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'observation':str(out),'sha256':sha(out),'bindings_checked':len(bindings),'actual_author_Lean':38,'new_author_modules':16,'root_math':0,'Judge20_started':False,'victory':False}))
