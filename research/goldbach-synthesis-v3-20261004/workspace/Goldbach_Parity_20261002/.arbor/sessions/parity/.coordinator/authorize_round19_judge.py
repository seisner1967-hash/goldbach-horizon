"""Verify frozen metadata, issue the unique gate; never run Judge or Lean."""
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); J=B/'round19/judge'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
prep=read(J/'preparation.json'); frozen='4763b4463708b6458186cd9872c94010c055487443801915e7fd487e307c7dae'
assert sha(J/'preparation.json')==frozen
assert prep['status']=='READY_AFTER_FROZEN_FINALS_NOT_EXECUTED'
assert not prep['independent_audit_yet_executed'] and prep['Judge_audit_Lean_probe_invocations_in_preparation']==0
assert prep['all_required_FINALs_frozen'] and prep['new_module_count']==11
for field in ('final_input_sha256','historical_dependencies_sha256','new_module_sources_sha256'):
    for rel,digest in prep[field].items(): assert sha(B/rel)==digest,(field,rel)
for name,digest in prep['judge_code_sha256'].items(): assert sha(J/name)==digest,name
for path,digest in prep['original_documents_sha256'].items(): assert sha(Path(path))==digest,path
assert sha(Path(prep['lean_executable']))==prep['lean_sha256']
assert sha(Path(prep['python_executable']))==prep['python_sha256']
assert sha(Path(prep['mathlib_HEAD_path']))==prep['mathlib_HEAD_sha256']
receipt=read(J/'freeze_metadata_receipt.json')
assert receipt['exit_code']==0 and receipt['preparation_sha256']==frozen
assert sha(J/'freeze_inputs_source_PREEXEC.py.txt')==sha(J/'freeze_inputs.py')==receipt['source_PREEXEC_sha256']
assert sha(J/'freeze_metadata_started.json')==receipt['started_sha256']
assert sha(J/'freeze_metadata.log')==receipt['log_sha256']
assert read(J/'final_read_review.json')['status']=='ALL_REQUIRED_FINALS_FULLY_READ_METADATA_ONLY'
assert read(C/'messages/round19_final3_root_observation.json')['author_PASS']==6
assert read(C/'messages/round19_final4_root_observation.json')['author_PASS']==5
assert not (J/'authorization.json').exists() and not (J/'audit_started.json').exists()
auth={'authorization':'ROOT19_JUDGE_CANONICAL_ATTEMPT01','root_authorized':True,'round':19,'role':5,
 'all_required_FINALs_inspected':True,'independent_new_module_compile_authorized':True,
 'canonical_NEW_numeric_results_inspected':True,'preparation_sha256':frozen,
 'judge_code_sha256':prep['judge_code_sha256'],'issued_utc':datetime.now(timezone.utc).isoformat(),
 'source_FULL_read_chunks':['e6f939','42cb18','9044d3','cb1796','9250ed'],
 'frozen_preparation_FULL_read_chunks':['1e4e53','84e72c'],
 'root_exec_scope':'metadata only; independent Judge owns the one audit and fresh11 Lean invocations',
 'old_producer_or_Lean_or_PASS_replay_authorized':False,'victory':False}
with (J/'authorization.json').open('x',encoding='utf-8') as f: f.write(json.dumps(auth,ensure_ascii=False,indent=2)+'\n')
obs={'status':'ROOT_VERIFIED_FINAL19_PREPARATION_UNIQUE_INDEPENDENT_JUDGE_GATE_ISSUED',
 'observed_utc':auth['issued_utc'],'preparation_sha256':frozen,'authorization_sha256':sha(J/'authorization.json'),
 'frozen_inputs_verified':len(prep['final_input_sha256']),
 'historical_dependencies_verified':len(prep['historical_dependencies_sha256']),
 'new_modules':11,'root_audit_compiler_numeric_invocations':0,'victory':False}
with (C/'messages/round19_judge_freeze_root_observation.json').open('x',encoding='utf-8') as f:
    f.write(json.dumps(obs,ensure_ascii=False,indent=2)+'\n')
cp=read(C/'checkpoint.json'); cp['phase']='ROUND19_INDEPENDENT_JUDGE_AUTHORIZED_ACTUAL_START_PENDING'
cp['last_progress']+=' All FINALs/full11source reads and immutable307prepinputs/26historicaldeps/runtime/originals verified; Judge prep4763 fullread, root unique gate issued. ActualJudge START not yet observed; official30/507 unchanged,noWin.'
cp['previous_goal_turn_evidence']+=['round19/judge/authorization.json', '.arbor/sessions/parity/.coordinator/messages/round19_judge_freeze_root_observation.json']
for row in cp['in_flight_executors']:
    if row['role']==5: row['status']='unique_concrete_gate_issued_actual_start_pending'
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
