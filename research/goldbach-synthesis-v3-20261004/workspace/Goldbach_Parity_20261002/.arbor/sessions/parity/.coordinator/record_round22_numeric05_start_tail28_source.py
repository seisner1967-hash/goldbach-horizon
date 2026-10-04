"""ROOT checkpoint metadata only; no candidate import or numerical evaluation."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
A = B / 'round22/role3/native_numeric_checker_only_consumer_source05_revision02/actual_numeric05_checker_only_attempt01'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
gate = C / 'messages/round22_native_numeric05_checker_only_authorization.json'
assert sha(gate) == 'e417407398e27d22a19a932bed6da09f09b0866bce8abbb2c08cfaaee28551cc'
start = read(A / 'checker_START.json')
parent = read(A / 'parent_START.json')
assert start['pid'] == 23088 and start['job_assigned'] and start['job_limit_flags_requested'] == 8968
assert parent['parent_invocations'] == 1 and parent['retry_count'] == 0
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
assert (cp['official_auxiliary_validation']['modules'], cp['official_auxiliary_validation']['declarations']) == (85, 1434)
o = dict(schema='ROUND22_ROOT_NUMERIC05_START_AND_TAIL_SOURCE_CHECKPOINT', time_utc=datetime.now(timezone.utc).isoformat(),
    actual_parent_tool='9e84a6/session81191', actual_closed=False, pid=23088,
    start_utc=start['utc'], parent_start_utc=parent['utc'], gate_sha256=sha(gate),
    parent_START_sha256=sha(A / 'parent_START.json'), checker_START_sha256=sha(A / 'checker_START.json'),
    source_review_repair='DEADLINE_NO_CREATION_CONTRACT_MISMATCH resolved by distinct SOURCE revision02',
    ROOT_draft_helpers_never_invoked=['authorize_round22_native_numeric05_checker_only.py', 'authorize_round22_native_numeric05_checker_only_v2.py'],
    selected_gate_helper='authorize_round22_native_numeric05_checker_only_v3.py',
    draft_v2_metadata_field_correction='SOURCE review uses candidate_runtime_calls; TRUST review uses produced_binary_invocations',
    tail_source_handoff_sha256='b80e83e1029995309836b313b5897a54ec5c27c07cb6e2a48371705c4cf41587',
    tail_source_review_pending=True, tail_compiled=False, numeric_verdict=False,
    ROOT_compiler_calls=0, ROOT_numeric_calls=0, native_refinement=False, D_N=False, WIN=False)
out = C / 'messages/round22_numeric05_start_tail_source_observation.json'
with out.open('x', encoding='utf-8') as f: json.dump(o, f, ensure_ascii=False, indent=2); f.write('\n')
cp['phase'] = 'ROUND22_NUMERIC05_ONE_CHECKER_RUNNING_TAIL_SOURCE_REVIEW'
cp['last_progress'] = 'Numeric05 one checker PID23088 running, no verdict; Gamma inversion27 PASS15 closed, official85/1434; Tail22 SOURCE review pending; D_N/WIN open.'
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
statuses = {3:'NUMERIC05_ROLE6_ONE_CHECKER_RUNNING_NO_RETRY', 4:'GAMMA_BRIDGE_SOURCE_PENDING_TAIL_PASS', 5:'TAIL_SOURCE_REVIEW_NO_COMPILER'}
for actor in cp['in_flight_executors']:
    if actor['role'] in statuses: actor['status'] = statuses[actor['role']]
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as f: f.write('\n'+cp['last_progress']+'\n')
print(json.dumps(o, ensure_ascii=False, indent=2))
