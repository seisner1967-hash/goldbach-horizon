"""Root records actual pre-Lean Judge failure; never executes the audit."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
J=B/'round17/judge'
def h(p):return sha256(p.read_bytes()).hexdigest()
p=J/'launch_receipt.json';r=json.loads(p.read_bytes())
assert r['exit_code']==1
assert h(J/'run-audit.py')==h(J/'audit_source.py.txt')==r['source_sha256']==r['snapshot_sha256']=='72dfe2d380e173948899d14e5334d96ed4cdca2c5149fe3d0ea3482e944e740b'
assert h(J/'audit.log')==r['log_sha256']=='e6c340a5f28473a04c44d3709c82b9401b496e445023a6d4bb7c99ac7a9a0ae5'
assert h(J/'launch_started.json')==r['started_marker_sha256']
assert h(J/'input_sha256.json')==r['input_manifest_sha256']=='40076625c36a04c5cef48ece8ee2d4fe625715cfbe1bf06364ae3da5b182bcb1'
assert h(J/'launch-audit-once.py')=='9c6f393b7db17d927d132a820b4347282775277633df34fad1e51d7bd4cf651d'
log=(J/'audit.log').read_text(encoding='utf-8')
assert 'FROZEN_INPUTS_AND_799_PRESERVED' in log and '454_STRICT_POSITIONS_VERIFIED' in log
assert 'FRESH_LEAN_STARTED' not in log and not (J/'build').exists()
assert "row['small_factor_exclusion_verified']" in log
obs=dict(status='REAL_JUDGE_ATTEMPT1_EXIT1_PRE_LEAN',attempts=1,exit_code=1,Lean_invocations=0,
         classification='checker incorrectly required applicability flag true on all252 physical controls',
         correct_guard='witness exists and e mod ell equals witness j mod ell; otherwise excluded remains false',
         frozen143_initial33_C4_15_390plus64_preservation799_PASS=True,
         source_sha256=r['source_sha256'],log_sha256=r['log_sha256'],launch_receipt_sha256=h(p),
         failed_attempt_preserved=True,continuation_requested_for_remaining_steps=True,
         root_did_not_rerun_audit_or_banks=True,mathematical_identity_failure=False,victory=False)
(C/'messages/round17_root_judge_attempt1_observation.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=json.loads(p.read_bytes())
cp['phase']='ROUND17_JUDGE_ACTUAL_PRE_LEAN_EXIT1_CONDITIONAL_FLAG_REPAIR'
cp['in_flight_executors']=['round17_judge: original attempt1 exit1 preserved before Lean, frozen143/799/33+15/454 passed; limited continuation of remaining checks and five new compiles being prepared']
cp['last_progress']+=' Actual Judge attempt1 at20:40:07 UTC exits1 before Lean after preservation799/frozen143/33+15/454PASS. Incorrect unconditional requirement for small_factor_exclusion_verified on252 controls; actual producer sets excluded=False unless witness exists and e congruent witness.j mod ell, then theta=0 and raw primepower factor ell. Root full reads source condition/log/receipt and verifies failed source/snapshot72dfe2/log e6c340. Continuation only remaining checks authorized with distinct immutable artifacts; never claim one successful audit when actual first attempt failed. No math identity or parity failure, no new independent compilation yet.'
cp['previous_goal_turn_evidence']+=['round17/judge/launch_receipt.json','round17/judge/audit.log','.arbor/sessions/parity/.coordinator/messages/round17_root_judge_attempt1_observation.json']
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:
    f.write('\nLe premier audit indépendant17, réellement lancé à20:40:07UTC, sort1 avant tout Lean. Conservation799, gel143, bindings33+15 et454 certificats stricts ont passé. Le contrôleur imposait à tort le drapeau small_factor_exclusion_verified à tous252 candidats ; ce drapeau n\'est vrai que lorsque le témoin existe et e≡j modulo son petit premier. La source numérique conservait correctement cette garde et les axes theta/raw. Source, snapshot, journal et reçu du Juge restent figés. Une continuation distincte des étapes restantes est autorisée ; aucun rerun des banques ou des signes, aucun échec analytique de parité inventé et aucun cumul Lean17 encore acquis.\n')
print(json.dumps(obs))
