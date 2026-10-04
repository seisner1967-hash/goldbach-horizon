"""Read actual completed Judge bytes, prints and stored encodings; no reexecution."""
import sys, json, hashlib, re
sys.set_int_max_str_digits(0)
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); J=B/'round19/judge'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''): h.update(block)
    return h.hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def verify(bindings):
    for rel,digest in bindings.items(): assert sha(B/rel)==digest,rel
a=read(J/'audit_receipt.json'); launch=read(J/'launch_receipt.json'); inputs=read(J/'input_manifest.json')
assert sha(J/'audit_receipt.json')==launch['audit_receipt_sha256']=='758e6fe25589d37d0e75d12317fe3cfca34015761df31f8e3df735a392331057'
assert sha(J/'audit.log')==launch['log_sha256']=='912a9dbfb9b23f8bd37751b553c5f57b545bf324ce46cc14cafb3936089eb6e3'
assert launch['exit_code']==0 and a['status']=='PASS_INDEPENDENT_ROUND19_AUXILIARY_ONLY'
assert sha(J/'input_manifest.json')==a['input_manifest_sha256']==launch['input_manifest_sha256']=='e3f8bc9d3ad8cbd4649d86ba5bf3fa4680eb12ae802ed6901f668127991280df'
verify(inputs['final_input_sha256']); verify(inputs['historical_dependencies_sha256'])
assert a['new_counts']=={'modules':11,'theorems':185,'defs':78,'structures':3,'instances':0,'axiom_prints':268}
assert a['previous_counts']=={'modules':30,'theorems':507} and a['cumulative_counts']=={'modules':41,'theorems':692}
stages={'01_preservation':'preservation_before','02_stored_numeric':'stored_numeric',
 '03_nonss_stored_integers':'nonss_stored_integer_checks','04_rank_stored_integers':'rank_stored_integer_checks',
 '06_fresh_independent_Lean':'independent_Lean','07_preservation_after':'preservation_after'}
for name,key in stages.items(): assert read(J/(name+'_PASS.json'))==a[key],name
assert read(J/'05_author_actual_attempts_PASS.json')['totals']==a['author_invocation_totals']=={'invocations':29,'failures':18,'invocations_with_warnings':9}
assert a['preservation_before']==a['preservation_after']=={'exact_protected_inventory':1361,'hashes_preserved':True,'old_scripts_or_Lean_or_PDF_executed':False}
rows=a['independent_Lean']['modules']; assert len(rows)==11
total=Counter(); warnings=[]; names=[]
for row in rows:
    n=row['module']; assert row['status']=='PASS_FRESH_NEW_INDEPENDENT_LEAN' and row['exit_code']==0
    assert read(J/(n+'_receipt.json'))==row
    inv=read(J/(n+'_actual_invocation.json'))
    for key,value in inv.items(): assert row[key]==value,(n,key)
    assert inv['exit_code']==0 and inv['subprocess_launch_error'] is None
    for key in ('source','source_original','source_snapshot'): assert sha(Path(row[key]))==row['source_sha256']
    for key in ('olean','log','stdout','stderr'): assert sha(Path(row[key]))==row[key+'_sha256'],(n,key)
    assert Path(row['log']).read_bytes()==Path(row['stdout']).read_bytes()+Path(row['stderr']).read_bytes()
    assert str(B/'round19/role3') not in row['LEAN_PATH'] and str(B/'round19/role4') not in row['LEAN_PATH']
    for dep,digest in row['fresh_import_olean_sha256'].items(): assert sha(J/'build'/(dep+'.olean'))==digest
    log=Path(row['log']).read_text(encoding='utf-8'); assert 'error:' not in log and 'sorryAx' not in log
    parsed={name:re.findall(r'[A-Za-z_][A-Za-z0-9_.]*',axs) for name,axs in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)}
    parsed.update({name:[] for name in re.findall(r"'([^']+)' does not depend on any axioms",log)})
    assert parsed==row['axioms'] and set(parsed)==set(row['requested_axiom_prints'])
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in parsed.values())
    ws=[s for s in log.splitlines() if 'warning:' in s]; assert ws==row['actual_warning_lines']
    assert not ws or (n=='RankCalibrationUnitLoss' and len(ws)==3)
    warnings+=ws; total.update(row['declaration_counts']); names.append(n)
assert total=={'theorem':185,'def':78,'structure':3} and len(warnings)==3
assert sum(row['axiom_prints'] for row in rows)==268
events=[json.loads(s) for s in (J/'audit.log').read_text(encoding='utf-8').splitlines()]
assert sum(e['stage']=='STAGE_STARTED' for e in events)==sum(e['stage']=='STAGE_PASS' for e in events)==7
assert sum(e['stage']=='ACTUAL_FRESH_NEW_LEAN_STARTED' for e in events)==sum(e['stage']=='FRESH_NEW_INDEPENDENT_LEAN_PASS' for e in events)==11
assert events[-1]['stage']=='ACTUAL_JUDGE19_FINISHED' and not list(J.glob('*continuation*'))
cert_summary={}
for bank,spec in inputs['numeric_banks'].items():
    data=read(B/spec['result']); stored=a['stored_numeric'][bank]; labels=Counter()
    for index in stored['stored_certificate_index']:
        value=data
        for part in index['json_pointer'].split('/')[1:]:
            key=part.replace('~1','/').replace('~0','~')
            value=value[int(key)] if isinstance(value,list) else value[key]
        encoded=json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode('utf-8')
        assert hashlib.sha256(encoded).hexdigest()==index['stored_certificate_sha256']
        assert value['sign']==index['stored_sign_label']; labels[value['sign']]+=1
    assert len(stored['stored_certificate_index'])==stored['stored_certificate_positions_including_repeated_JSON_fields']
    assert dict(labels)==stored['stored_sign_labels']
    assert stored['actual_exit_code']==0 and not stored['new_logarithmic_signs_computed'] and not stored['producer_kernel_log_or_replay_executed']
    cert_summary[bank]={'stored_positions':len(stored['stored_certificate_index']),'stored_sign_labels':dict(labels)}
    del data
for key in ('victory','parity_obstacle_bypass_proved','full_fixed_D_N_ledger_paid','producer_kernel_log_or_new_sign_called','old_Lean_or_PDF_or_preflight_script_executed','source_onset_applied_to_N_10power8'): assert a[key] is False,key
obs={'status':'ROOT_VERIFIED_ACTUAL_JUDGE19_AUDIT_EXIT0_FULL_FINAL_CLOSURE_PENDING',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'actual_started_utc':launch['started_at_utc'],'actual_finished_utc':launch['finished_at_utc'],
 'audit_receipt_sha256':sha(J/'audit_receipt.json'),'launch_receipt_sha256':sha(J/'launch_receipt.json'),
 'frozen_inputs_verified':307,'historical_dependencies_verified':26,'new_counts':a['new_counts'],
 'actual_independent_Lean_invocations':11,'actual_independent_Lean_failures':0,'actual_independent_style_warnings':warnings,
 'FULL_root_log_read_chunks':['de258a','2491c5','2988f3'],'stored_certificates_hash_and_labels_only':cert_summary,
 'new_log_or_sign_evaluation_by_root':False,'root_compiler_audit_producer_invocations':0,
 'official_counts_not_recorded_until_FINAL5_closed':True,'semantic_obligations':a['semantic_obligations'],'victory':False}
with (C/'messages/round19_judge_finish_root_observation.json').open('x',encoding='utf-8') as f: f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND19_ACTUAL_INDEPENDENT_AUDIT_VERIFIED_FINAL_CLOSURE_PENDING'
cp['last_progress']+=' Actual independentJudge19 exit0 finished '+launch['finished_at_utc']+' verified11freshPASS185thm78defs3str268standardprints/3benignwarnings,7stages/all307inputs/26deps/49281storedcertificatehashes+labels,0replays. FINAL5closure pending; officialcounts unchanged until closed,noWin.'
cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round19_judge_finish_root_observation.json')
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in obs.items() if k not in ('semantic_obligations','actual_independent_style_warnings')},ensure_ascii=False,indent=2))
