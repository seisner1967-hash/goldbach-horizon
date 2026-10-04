"""Record real candidate failures and root source review; no compiler call."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round19'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def save(p,obj):
    with p.open('x',encoding='utf-8') as f: f.write(json.dumps(obj,ensure_ascii=False,indent=2)+'\n')
prep=read(R/'role3/preparation.json')
review={m['module']:m['sha256'] for m in prep['written_modules']}
for module,digest in review.items(): assert sha(R/'role3'/(module+'.lean'))==digest,module
assert sha(R/'role3/build_once.py')==prep['launcher_sha256']
for name,digest in {
 'SeparatedTypeII.lean':'4513f3323bbf475b329daf423de805eb207d3fe88793f91016369bcb0d5228d7',
 'SeparatedTypeII.olean':'896daceeb6a093f808313556ee63a93761ecd5831bc6279b8b88ffe9212d1dd5',
 'SeparatedTypeIICount.lean':'55ac598030d5bd67202553a5a8ffffc6fcc2ba3aa796428808aecb9586d5d5d1',
 'SeparatedTypeIICount.olean':'5ee894fa6a17f05bca328f743783ede1c27b40bd2e465efb22364b106f45a2fc'
}.items(): assert sha(R/'../round18/judge/build'/name)==digest,name
save(C/'messages/round19_role3_source_root_observation.json',{
 'status':'ROOT_FULL_READ_SIX_ROLE3_SOURCES_AND_BUILD_SCHEMA_ONLY_NO_COMPILE_GATE',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'sources':review,
 'builder_sha256':prep['launcher_sha256'],'preparation_sha256':sha(R/'role3/preparation.json'),
 'source_only_counts':prep['written_totals_not_compiler_results'],
 'compiler_results':None,'numeric_rank_PASS_inspected':False,
 'open_effective_coefficient_positivity_K14_K18_GammaRank_ledger':True,
 'former_role3_handle_finished_and_reaped':True,'victory':False})
ledger=read(R/'role4/build_receipt.json')
row=next(x for x in ledger['attempts'] if x['attempt']==1)
assert row['exit_code']==1 and row['phase']=='FINISHED'
assert row['source_sha256']=='36307959fc9e0d968be0e39fca9899036351158ad4c048de71cc5f6dcd321966'
for pathkey,shakey in [('snapshot','snapshot_sha256'),('builder_snapshot','builder_snapshot_sha256'),
                       ('started_receipt','started_receipt_sha256'),('log','log_sha256')]:
    assert sha(Path(row[pathkey]))==row[shakey]
assert row['builder_snapshot_sha256']=='fd59294942a1bab559b929f2678a51808fb19c33717a0ee3775821bd8ef08641'
assert row['compiler_sha256']=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
failure={
 'status':'ROOT_READ_ACTUAL_FAILED_LEAN19_ROLE4_ATTEMPT01',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'round':19,'node':'14.4',
 'actual_attempt':row,'source_and_full_log_read':True,'actual_exit_code':1,
 'errors':[
  {'line':29,'kind':'elaboration','detail':'Finset.le_sup function id not inferred'},
  {'line':70,'kind':'proof term','detail':'n / n = 1 remains; division self requires positive proof'},
  {'line':120,'kind':'tactic recursion','detail':'Concrete norm_num prime-factor unfolding exceeded maxRecDepth'}],
 'source_sorry_admit_or_added_axioms':False,
 'failed_declarations_internal_sorryAx_printed':True,
 'accepted_PASS_or_victory':False,'parity_inference_failure':False,
 'repair_scope':'Explicit id and positive proof, abstract prime-power extraction, kernel-decided quotient/gcd; preserve failed source and log.',
 'numeric_replay_or_old_Lean_recompile':False}
save(C/'messages/round19_lean_failure01_root.json',failure)
launcher=read(R/'role4/launcher_failed01.json')
assert launcher['actual_Lean_invocations']==0 and launcher['exit_code']==1
assert sha(R/'role4'/launcher['source_snapshot'])==launcher['source_sha256']
assert sha(R/'role4/launcher_failed01.log')==launcher['log_sha256']
save(C/'messages/round19_launcher_failure01_root.json',{
 'status':'ROOT_READ_ACTUAL_PYTHON_PARSE_FAILURE_BEFORE_ANY_COMPILER',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'actual_incident':launcher,
 'corrected_builder_full_read_sha256':row['builder_snapshot_sha256'],
 'mathematical_failure':False,'victory':False})
cp_path=C/'checkpoint.json'; cp=read(cp_path)
cp['phase']='ROUND19_NONSS_PASS_ROLE4_ACTUAL_LEAN_REPAIR_RANK_BANK_PREPARING_JUDGE_DRAFT_REVIEW'
cp['in_flight_executors']=[
 {'role':3,'agent':None,'status':'six_sources_FULL_ROOT_READ_READY_former_handle_reaped_waits_rank_numeric_PASS'},
 {'role':4,'agent':'/root/round19_formal4_nonss','status':'actual_Lean_attempt01_exit1_technical_repair_authorized'},
 {'role':6,'agent':'/root/round18_content_review','status':'nonSS_FINAL_PASS_no_replay_rank_bank_preparing_only'},
 {'role':5,'agent':'/root/round19_judge','status':'actual_fresh_semantic_DRAFT_review_NO_COMPILER_AUDIT_GATE'}]
cp['last_progress']+=' New nonSS19 unique canonical exit0 confirmed and final25 bindings/13captures fully byte-verified; concrete formal4 gate26 numeric bindings issued after fullcurrent5sources review. First actual role4 Lean attempt01 exit1 has three technical elaboration/division/recursion errors and internal sorryAx in failed declarations, no source sorry or mathematical parity failure; log/source/start/exit preserved. One launcher Python parse failure occurred earlier before any Lean and is separately preserved with honest POSTEXEC source. Corrected builder FULLread. Role3 sixsources/build/schema FULLread85source-only statements; K14 effective coefficient positivity, source K18 and GammaRank open. FormerR3 finished/reaped, fresh independentJudge19 actually spawned for DRAFT semantic/source review only; no Judge compiler gate. Rank13.11 bank source preparation ongoing; no13.11 producer/Lean. Official30/507 unchanged, noWin.'
for rel in [
 '.arbor/sessions/parity/.coordinator/messages/round19_nonss_finish_root_observation.json',
 'round19/role4/root_compile_authorization.json',
 '.arbor/sessions/parity/.coordinator/messages/round19_role3_source_root_observation.json',
 '.arbor/sessions/parity/.coordinator/messages/round19_lean_failure01_root.json',
 '.arbor/sessions/parity/.coordinator/messages/round19_launcher_failure01_root.json']:
    if rel not in cp['previous_goal_turn_evidence']: cp['previous_goal_turn_evidence'].append(rel)
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'ACTUAL_FAILED_COMPILER_AND_SOURCE_REVIEW_RECORDED_NO_OFFICIAL_COUNT_CHANGE',
 'failed_Lean_attempts_observed':1,'launcher_failures_before_Lean':1,'sources_role3_full_read':6,'victory':False}))
