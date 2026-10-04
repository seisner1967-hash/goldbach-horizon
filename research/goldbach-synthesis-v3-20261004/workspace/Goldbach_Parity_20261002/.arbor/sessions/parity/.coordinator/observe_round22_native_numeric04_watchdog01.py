"""ROOT metadata-only observation of real WATCHDOG04; no payload evaluation."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role3/native_numeric_consumer_source01'
A = P / 'actual_numeric04_attempt01'
E = B / 'round22/role3/native_numeric_closure_source01'
G = C / 'messages/round22_native_numeric04_authorization.json'

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
    return digest.hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def check(path, digest, size=None):
    assert path.is_file() and sha(path) == digest, str(path)
    assert size is None or path.stat().st_size == size, str(path)

def binding(row):
    check(Path(row['path']), row['sha256'], row['bytes'])

parser = argparse.ArgumentParser()
parser.add_argument('--ROOT-full-reads', required=True)
args = parser.parse_args()
closed_path = E / 'numeric_execution_closure22.json'
evidence_path = E / 'closure_evidence_bindings22.json'
quiescence_path = E / 'quiescence_evidence22.json'
check(closed_path, 'a99a5e58768d09a16c7a1ae248448be41016cac228fc57c69372d6abb2774df3')
check(evidence_path, 'ad229461cba2a9b411801c024e443148b9ba2673508107e868a173b42c0ea184')
check(quiescence_path, '2763645031ab61fdbeae88a8cd5d699d4a11b60381f132dd8e5c5da2ba94402a')
check(G, 'b5dc57f1afa98304645f9e62505026c805c7a536946a15eedec399922aeba932')
watchdog_path = A / 'WATCHDOG_TERMINATION_REQUEST.json'
check(watchdog_path, 'cd559e4e5a3355639dfe3d46d358537ee3ee9984d29206efa1781fc7f7e1f706')
closed, evidence, quiet, gate, pre, watchdog = map(read,
    (closed_path, evidence_path, quiescence_path, G, A / 'PRE.json', watchdog_path))
assert closed['schema'] == 'ROUND22_NATIVE_NUMERIC04_EXTERNAL_METADATA_CLOSURE'
assert closed['status'] == 'CLOSED_STOP_NO_MATHEMATICAL_VERDICT'
assert closed['session_id'] == quiet['session_id'] == 17351
assert closed['parent_exit_code'] == quiet['parent_exit_code'] == 1
assert closed['session_closed_tool_chunk'] == quiet['session_closed_tool_chunk'] == 'b762cb'
assert closed['parent_invocations'] == 1 and closed['retry_count'] == 0
assert closed['actual_parent_receipt_sha256'] is None
for name in ('actual_parent_receipt_present', 'parent_POST_present', 'parent_POST_verified',
             'coefficient_report_present', 'synthetic_parent_receipt_created',
             'mathematical_falsity_established', 'coefficient_or_interval_arithmetic_recomputed_here',
             'native_Lean_refinement', 'B40_real_log_refinement_Lean', 'effective_loads_observed',
             'universal_loader_closure_verified', 'spectral_H1', 'D_N', 'WIN'):
    assert closed[name] is False, name
assert closed['compiler_invocations'] == closed['native_invocations_here'] == closed['mutant_runs'] == 0
assert closed['all_current_bytes_preserved'] and closed['actual_processes_quiescent']
assert closed['external_physical_preservation_distinct_from_parent_POST']
assert quiet['parent_session_complete'] and quiet['known_created_child_pids_absent']
assert quiet['known_created_child_pids'] == [32676, 6864] and quiet['matching_known_processes'] == []
assert quiet['gate_sha256'] == closed['gate_sha256'] == pre['gate_sha256'] == sha(G)
assert quiet['actual_status'] == watchdog['status'] == 'HARD_WALL_NO_VERDICT_POST_UNVERIFIED'
assert watchdog['wall_seconds'] == 3600 and watchdog['conservation_verified'] is False
for name in ('receipt.json', 'POST.json', 'checker_FIN.json', 'coefficient_result.json'):
    assert not (A / name).exists(), name
producer_start, checker_start, producer_fin = map(read,
    (A / 'producer_START.json', A / 'checker_START.json', A / 'producer_FIN.json'))
assert [producer_start['pid'], checker_start['pid']] == quiet['known_created_child_pids']
assert producer_fin['pid'] == 32676 and producer_fin['exit_code'] == 0
assert producer_fin['wait_signalled'] and producer_fin['job_empty_confirmed']
assert producer_fin['api_or_control_error'] is None and producer_fin['pipe_faults'] == []
assert closed['produced_binary_processes_created'] == 2
assert evidence['schema'] == 'ROUND22_NATIVE_NUMERIC04_CLOSURE_EVIDENCE_BINDINGS'
assert evidence['scope'] == 'EXTERNAL_PHYSICAL_METADATA_AFTER_QUIESCENCE'
assert evidence['native_invocations_here'] == 0
assert evidence['output_bindings'] == closed['output_bindings']
for name in ('gate', 'manifest', 'preparation', 'PRE', 'quiescence_evidence'):
    binding(evidence[name])
rows = read(P / 'numeric_manifest22.json')['bindings']
assert len(rows) == gate['inputs_verified'] == pre['binding_count'] == closed['inputs_verified'] == 6456
for row in rows:
    binding(row)
assert len(pre['captures']) == len(evidence['captures']) == closed['capture_original_copy_pairs_verified'] == 66
for actual, recorded in zip(pre['captures'], evidence['captures']):
    assert recorded['original']['path'] == actual['original'] and recorded['copy']['path'] == actual['copy']
    assert recorded['original']['sha256'] == recorded['copy']['sha256'] == actual['sha256']
    binding(recorded['original'])
    binding(recorded['copy'])
assert [{key: row[key] for key in ('path', 'sha256')} for row in evidence['metadata_controls']] == gate['metadata_control_bindings']
assert len(evidence['metadata_controls']) == closed['metadata_controls_verified'] == 5
for row in evidence['metadata_controls']:
    binding(row)
assert len(closed['output_bindings']) == 83
assert {Path(row['path']).resolve() for row in closed['output_bindings']} == {
    path.resolve() for path in A.rglob('*') if path.is_file()}
for row in closed['output_bindings']:
    binding(row)
registry_path = B / 'round22/previous_artifacts_sha256.json'
check(registry_path, '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99')
archives = read(registry_path)['sha256']
assert len(archives) == closed['protected_archives_verified'] == 3089
for relative, digest in archives.items():
    path = (B / relative).resolve()
    assert path.is_relative_to(B.resolve())
    check(path, digest)
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
official = cp['official_auxiliary_validation']
observation = dict(schema='ROUND22_ROOT_NATIVE_NUMERIC04_WATCHDOG_CLOSED_OBSERVATION',
    utc=datetime.now(timezone.utc).isoformat(), actual_status=watchdog['status'],
    parent_invocations=1, retry_count=0, parent_exit_code_observed=1,
    actual_session_closed_chunk='b762cb', created_callbacks=[32676, 6864],
    producer_exit_code=0, checker_exit_code=None, checker_FIN_present=False,
    parent_receipt_present=False, actual_parent_receipt_sha256=None,
    parent_POST_present=False, parent_POST_verified=False,
    numerical_verdict_level='STOP_NO_MATHEMATICAL_VERDICT', coefficient_result_present=False,
    external_conservation_verified=True, all_current_bytes_preserved=True,
    inputs_verified=6456, captures_verified=66, archives_verified=3089,
    metadata_controls_verified=5, output_bindings_verified=83,
    external_quiescence_verified=True, quiescence_scope=closed['quiescence_scope'],
    closure_sha256=sha(closed_path), evidence_sha256=sha(evidence_path),
    quiescence_sha256=sha(quiescence_path), watchdog_sha256=sha(watchdog_path),
    ROOT_full_reads=args.ROOT_full_reads,
    large_evidence_scope='all metadata rows parsed and all bound bytes rehashed; no payload parsing/evaluation',
    official_modules=official['modules'], official_declarations=official['declarations'],
    Lean_credit_from_numerical_attempt=0, ROOT_compiler_invocations=0, ROOT_numeric_invocations=0,
    native_Lean_refinement=False, mathematical_falsity_established=False,
    effective_loads_observed=False, universal_loader_closure_verified=False,
    spectral_H1=False, D_N=False, WIN=False)
out = C / 'messages/round22_native_numeric04_closed_observation.json'
with out.open('x', encoding='utf-8') as stream:
    json.dump(observation, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
cp['phase'] = 'ROUND22_NATIVE_NUMERIC04_WATCHDOG_CLOSED_GLOBAL_OBLIGATIONS_OPEN'
cp['last_progress'] = 'Numeric04 closed after actual3600s WATCHDOG; no parent receipt/POST/coefficient; external preservation paid; no mathematical verdict.'
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
cp['native_numeric04_closed_observation'] = observation
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as stream:
    stream.write('\nNumeric04 actual WATCHDOG3600s, parent exit1, producerexit0, checkerFIN/receipt/POST/coefficient absent; external conservation6456/66/3089/5/83 verified; no mathematical verdict, zero Lean credit, D_N/WIN OPEN.\n')
print(json.dumps(observation, ensure_ascii=False, indent=2))
