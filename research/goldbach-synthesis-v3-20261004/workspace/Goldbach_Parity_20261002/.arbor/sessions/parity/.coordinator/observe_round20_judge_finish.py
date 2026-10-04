"""Observe finished independent receipts/bytes, never reexecute their audit."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';J=B/'round20/judge'
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()
a=load(J/'audit_receipt.json');l=load(J/'launch_receipt.json');post=load(J/'launch_post_integrity.json')
i=load(J/'input_manifest.json');s=load(J/'audit_started.json')
assert a['status']=='PASS_INDEPENDENT_ROUND20_AUXILIARY_ONLY'
assert l['actual_exit_code']==0 and l['launch_error'] is None
assert post['credited_pass'] and post['all_frozen_bindings_unchanged'] and post['changed_inputs']==[]
assert a['new_counts']=={'modules':16,'theorems':250,'defs':83,'structures':1,'axiom_prints':334}
assert a['cumulative_counts']=={'modules':57,'theorems':942}
assert a['author_attempts']['totals']=={'actual_invocations':38,'actual_PASS':16,'actual_FAIL':22}
assert a['score']==0 and not a['victory'] and not a['whole_D_N_target_proved']
assert not a['parity_obstacle_bypass_proved'] and not a['full_fixed_D_N_ledger_paid']
assert sha(J/'audit_receipt.json')==l['audit_receipt_sha256']
assert sha(J/'audit.log')==l['audit_log_sha256']
assert s['input_manifest_sha256']==sha(J/'input_manifest.json')=='c37af3ac54572855e80a124f1f4f733997fbd61a6d7152be3205522e7b2c4305'
assert i['authorization_sha256']==sha(J/'authorization.json')=='a321f065d36d8d18529d12356d2502e12a75e78fd87a59effeb6db562fba7c03'
assert i['preparation_sha256']==sha(J/'preparation.json')=='fe440243022cf4111c61827f7b6a387e4a2182cd3523b4aef41ae411abcda6a7'
bindings={}
for group in ['final_input_sha256','historical_dependencies_sha256','numeric_frozen_sha256','new_module_sources_sha256','previous_artifacts_sha256','original_documents_sha256','runtime_bindings_sha256']:
    for name,h in i[group].items():
        p=Path(name)
        if not p.is_absolute():p=B/p
        assert str(p) not in bindings or bindings[str(p)]==h
        bindings[str(p)]=h
for path,h in bindings.items():assert sha(path)==h,path
modules=[];warnings=[]
for row in a['independent_Lean']['modules']:
    name=row['module']; receipt=J/(name+'_receipt.json');raw=load(J/(name+'_actual_invocation.json'))
    assert load(receipt)==row
    assert raw['actual_exit_code']==row['actual_exit_code']==0 and row['status']=='PASS_FRESH_INDEPENDENT_LEAN'
    assert raw['output_olean_exists'] and raw['launch_error'] is None
    start=load(J/(name+'_started.json')); p=Path(row['source'])
    assert p.parent==J/'audit' and row['command']==[i['lean_executable'],'-o',str(p.with_suffix('.olean')),str(p)]
    assert start['command']==row['command'] and start['started_utc']==row['started_utc']
    assert sha(row['source_original'])==sha(row['source'])==sha(row['source_capture'])==row['source_sha256']
    assert sha(p.with_suffix('.olean'))==row['olean_sha256']==raw['olean_sha256']
    for value in row['outputs'].values():assert sha(value['path'])==value['sha256']
    pr=load(J/(name+'_post_integrity.json'))
    assert pr['all_frozen_bindings_unchanged'] and pr['source_copy_unchanged'] and pr['all_prior_fresh_oleans_unchanged']
    for folder in row['LEAN_PATH'].split(';'):
        assert not any(Path(folder).resolve().is_relative_to((B/'round20'/owner).resolve()) for owner in ['role3','role4','role4_geometry'])
    modules.append({'module':name,'actual_exit_code':0,'source_sha256':row['source_sha256'],
      'olean_sha256':row['olean_sha256'],'declaration_counts':row['declaration_specification']['declaration_counts'],
      'axiom_prints':row['axiom_prints'],'receipt_sha256':sha(receipt),'raw_receipt_sha256':sha(J/(name+'_actual_invocation.json'))})
    warnings.extend({'module':name,'line':line} for line in row['warning_lines'])
assert len(modules)==16
obs={'status':'ACTUAL_JUDGE20_EXIT0_SIXTEEN_INDEPENDENT_AUXILIARY_PASS_FINAL5_CLOSURE_PENDING',
 'observed_at_utc':datetime.now(timezone.utc).isoformat(),'actual_start':s['started_utc'],'actual_finish':l['finished_utc'],
 'audit_receipt_sha256':sha(J/'audit_receipt.json'),'launch_receipt_sha256':sha(J/'launch_receipt.json'),
 'launch_post_integrity_sha256':sha(J/'launch_post_integrity.json'),'audit_log_sha256':sha(J/'audit.log'),
 'new_counts':a['new_counts'],'candidate_cumulative_counts_pending_controller':a['cumulative_counts'],
 'actual_author_totals':a['author_attempts']['totals'],'all2837_input_bytes_reverified':len(bindings)==2837,
 'independent_module_receipt_observations':modules,'style_warnings':warnings,
 'semantic_obligations':a['semantic_obligations'],'stored_numeric_only':True,
 'root_compiler_audit_math_or_numeric_sign_invocations':0,'victory':False}
out=C/'messages/round20_judge_finish_root_observation.json'
with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(obs,f,ensure_ascii=False,indent=2);f.write('\n')
cp_path=C/'checkpoint.json';cp=load(cp_path)
cp['phase']='ROUND20_ACTUAL_JUDGE_EXIT0_SIXTEEN_FRESH_PASS_FINAL5_CLOSURE_PENDING'
for item in cp['in_flight_executors']:
    if item['role']==5:item['status']='ACTUAL_AUDIT_EXIT0_FRESH16_PASS_NO_FAILURE_FINAL5_PENDING'
cp['last_progress']+=' ActualJudge20 uniqueauditexit0/16freshPASS250thm83defs1str334stdprints; all2837inputs andsource/copy/capture/oleans/rawlogs/receipts verified asmetadata. OfficialcountscreditpendingFINAL5/controller. TruepartialsourceFriablebudget butF0minusF1/SD/bridge/wholeDN open, noWin.'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'observation_sha256':sha(out),'actual_start':s['started_utc'],'actual_finish':l['finished_utc'],'new_counts':a['new_counts'],'style_warnings':len(warnings),'root_math':0,'victory':False}))
