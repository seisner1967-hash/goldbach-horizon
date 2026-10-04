"""Observe second pre-Lean failure and ongoing new compiles; no audit run."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';J=B/'round17/judge'
def h(p):return sha256(p.read_bytes()).hexdigest()
p=J/'continuation_receipt.json';r=json.loads(p.read_bytes())
assert r['exit_code']==1
assert h(J/'continue-audit.py')==h(J/'continuation_source.py.txt')==r['source_sha256']==r['snapshot_sha256']=='2faf3564e16991ed6dc394972e390629e3bfe8abc516e951e416e14da7903caa'
assert h(J/'continuation.log')==r['log_sha256']=='86c7ad7801573126b4835abb6bda4cc0a83ee6aee8c27721a227590d22d7fca9'
assert h(J/'continuation_started.json')==r['started_marker_sha256']
log=(J/'continuation.log').read_text(encoding='utf-8');assert 'FRESH_LEAN_STARTED' not in log
obs=dict(status='ROOT_VERIFIED_SECOND_REAL_PRE_LEAN_JUDGE_EXIT1',exit_code=1,Lean_invocations_at_this_failure=0,
         classification='inactive205 candidate records retain kernel_ref and C_recipe with null; presence does not imply active reference',
         correct_guard='kernel_ref is not None, exactly47 active references and205 literal zeros',
         source_sha256=r['source_sha256'],log_sha256=r['log_sha256'],receipt_sha256=h(p),
         actual_Judge_failed_pre_Lean_runs=2,continuation02_active=True,
         no_identity_or_parity_failure=True,no_audit_or_producer_reran_by_root=True,victory=False)
(C/'messages/round17_root_judge_continuation1_observation.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=json.loads(p.read_bytes())
cp['phase']='ROUND17_TWO_PRE_LEAN_JUDGE_FAILURES_PRESERVED_FRESH_COMPILATIONS_ACTIVE'
cp['in_flight_executors']=['round17_judge: continuation02 actual; remaining stored arithmetic stages PASS and fresh Root/Powerset PASS, Selberg in flight; first two pre-Lean exit1 preserved',
                         'round13_formal3_switch: read-only schema review, no writes or executions, prior numerical FINALs frozen']
cp['last_progress']+=' Root fully reads both continuation sources and first-continuation log/receipt: second actual exit1 because205 inactive records have null reference keys, not omitted keys. Sources/logs/snapshots remain immutable; guards corrected only on remaining candidate stage. Continuation02 actually passes17488CRT/252candidates/A-R-S, fullTypeII162338/sixmasks/181beta and C4moments, preserves30producercompilations23errors/PASS15warning. Independent Roots and Powerset each exit0, standardaxioms and identicaloleans; Selberg fresh started. Root does not execute any audit/bank/compiler. Original2pre-Lean failures are not analytic parity failures.'
cp['previous_goal_turn_evidence']+=['round17/judge/continuation_receipt.json','round17/judge/continuation.log','round17/judge/continue-audit02.py','.arbor/sessions/parity/.coordinator/messages/round17_root_judge_continuation1_observation.json']
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs))
