"""ROOT external closure metadata observer. Never imports a candidate or computes a coefficient."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role3/native_numeric_checker_only_consumer_source05_revision02'
A = P / 'actual_numeric05_checker_only_attempt01'
Q = B / 'round22/role3/native_numeric_checker_only_closure_source05'
def read(p): return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): h.update(block)
    return h.hexdigest()
def check(p, digest, size=None):
    assert p.is_file() and sha(p) == digest, str(p)
    assert size is None or p.stat().st_size == size, str(p)

parser = argparse.ArgumentParser()
for name in ('closure-sha', 'evidence-sha', 'quiescence-sha', 'ROOT-full-reads'):
    parser.add_argument('--'+name, required=True)
args = parser.parse_args()
closed_path = Q / 'numeric_execution_closure22.json'
evidence_path = Q / 'closure_evidence_bindings22.json'
check(closed_path, args.closure_sha)
check(evidence_path, args.evidence_sha)
d, evidence = read(closed_path), read(evidence_path)
assert d['schema'] == 'ROUND22_NATIVE_NUMERIC05_CHECKER_ONLY_EXTERNAL_METADATA_CLOSURE'
assert d['session_id'] == 81191 and d['produced_binary_processes_created'] == 1
assert d['parent_invocations'] == 1 and d['retry_count'] == 0
assert d['all_current_bytes_preserved'] and d['actual_processes_quiescent']
assert (d['inputs_verified'], d['capture_original_copy_pairs_verified'], d['payload_original_copy_pairs_verified'], d['metadata_controls_verified'], d['protected_archives_verified']) == (6576,109,3,5,3089)
assert d['external_physical_preservation_distinct_from_parent_POST']
assert not d['synthetic_parent_receipt_created'] and not d['coefficient_or_interval_arithmetic_recomputed_here']
for name in ('D_N','WIN','native_Lean_refinement','B40_real_log_refinement_Lean','effective_loads_observed','universal_loader_closure_verified'):
    assert d[name] is False, name
quiescence_path = Path(d['quiescence_evidence_path'])
check(quiescence_path, args.quiescence_sha)
assert d['quiescence_evidence_sha256'] == args.quiescence_sha
quiescence = read(quiescence_path)
assert quiescence['parent_session_complete'] and quiescence['known_created_child_pids_absent']
assert quiescence['known_created_child_pids'] == [23088] and quiescence['session_id'] == 81191
assert quiescence['parent_exit_code'] == d['parent_exit_code']
assert quiescence['session_closed_tool_chunk'] == d['session_closed_tool_chunk']
gate_path = C / 'messages/round22_native_numeric05_checker_only_authorization.json'
check(gate_path, 'e417407398e27d22a19a932bed6da09f09b0866bce8abbb2c08cfaaee28551cc')
manifest_path = P / 'numeric_checker_only_manifest22.json'
check(manifest_path, 'a22738cdeabf910caa822ead788774cd4b574d54d4bb7a0aedaa242236d7e0d7')
rows = read(manifest_path)['bindings']
assert len(rows) == 6576 and len({str(Path(x['path']).resolve()).casefold() for x in rows}) == 6576
for x in rows: check(Path(x['path']), x['sha256'], x['bytes'])
for name, count in (('captures',109), ('payload_original_copy_pairs',3)):
    assert len(evidence[name]) == count
    for pair in evidence[name]:
        for endpoint in ('original','copy'):
            x = pair[endpoint]; check(Path(x['path']), x['sha256'], x['bytes'])
assert len(evidence['metadata_controls']) == 5
for x in evidence['metadata_controls']: check(Path(x['path']), x['sha256'], x['bytes'])
outputs = d['output_bindings']
assert outputs == evidence['output_bindings']
assert {str(x.resolve()).casefold() for x in A.rglob('*') if x.is_file()} == {str(Path(x['path']).resolve()).casefold() for x in outputs}
for x in outputs: check(Path(x['path']), x['sha256'], x['bytes'])
assert d['old04_outputs_preserved'] == 83 and d['old04_missing_receipt_POST_checkerFIN_coefficient_still_absent']
old_actual = B / 'round22/role3/native_numeric_consumer_source01/actual_numeric04_attempt01'
old_closed = read(B / 'round22/role3/native_numeric_closure_source01/numeric_execution_closure22.json')
assert {str(x.resolve()).casefold() for x in old_actual.rglob('*') if x.is_file()} == {str(Path(x['path']).resolve()).casefold() for x in old_closed['output_bindings']}
for name in ('receipt.json','POST.json','checker_FIN.json','coefficient_result.json'): assert not (old_actual / name).exists()
registry_path = B / 'round22/previous_artifacts_sha256.json'
check(registry_path, '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99')
registry = read(registry_path)['sha256']
assert len(registry) == 3089
for relative, digest in registry.items():
    p = (B / relative).resolve(); assert p.is_relative_to(B.resolve()); check(p, digest)
aux = d['status'] == 'CLOSED_PARENT_PAPER_AUX_RESULT_PENDING_NATIVE_REFINEMENT'
assert aux or d['status'] == 'CLOSED_STOP_NO_MATHEMATICAL_VERDICT'
assert d['actual_parent_receipt_present'] == (A / 'receipt.json').is_file()
assert d['parent_POST_present'] == (A / 'POST.json').is_file()
assert d['coefficient_report_present'] == (A / 'coefficient_result.json').is_file()
if d['actual_parent_receipt_present']:
    check(A / 'receipt.json', d['actual_parent_receipt_sha256'])
    r = read(A / 'receipt.json')
    assert r['parent_invocations'] == 1 and r['retry_count'] == 0 and r['D_N'] is False and r['WIN'] is False
if aux:
    assert d['parent_exit_code'] == 0 and d['parent_POST_verified'] and d['coefficient_report_present']
    assert r['status'] == 'PAPER_AUDITED_EXACT_INTEGER_PROJECTION_AUX_CHECKED_PENDING_NATIVE_REFINEMENT'
    assert r['failure'] is None and r['conservation_error'] is None
o = dict(schema='ROUND22_ROOT_NATIVE_NUMERIC05_EXTERNAL_CLOSED_OBSERVATION', time_utc=datetime.now(timezone.utc).isoformat(),
    actual_parent_tool='9e84a6/session81191', actual_status=d['parent_result_status'], external_status=d['status'],
    parent_exit_code=d['parent_exit_code'], session_closed_tool_chunk=d['session_closed_tool_chunk'],
    closure_sha256=args.closure_sha, evidence_sha256=args.evidence_sha, quiescence_sha256=args.quiescence_sha,
    external_conservation_verified=True, inputs_verified=6576, captures_verified=109, payload_pairs_verified=3, archives_verified=3089,
    parent_receipt_present=d['actual_parent_receipt_present'], parent_POST_present=d['parent_POST_present'], parent_POST_verified=d['parent_POST_verified'],
    coefficient_present=d['coefficient_report_present'], parent_paper_aux_result_observed=aux, coefficient_arithmetic_recomputed_by_ROOT=False,
    native_Lean_refinement=False, numeric_result_used_as_Lean_proof=False, ROOT_compiler_calls=0, ROOT_numeric_calls=0,
    ROOT_FULL_read_receipts=args.ROOT_full_reads, D_N=False, WIN=False)
out = C / 'messages/round22_native_numeric05_closed_observation.json'
with out.open('x', encoding='utf-8') as f: json.dump(o,f,ensure_ascii=False,indent=2); f.write('\n')
cp_path = C / 'checkpoint.json'; cp = read(cp_path)
cp['phase'] = 'ROUND22_NUMERIC05_CLOSED_GLOBAL_ANALYTIC_OBLIGATIONS_OPEN'
cp['last_progress'] = d['status']+'; external6576/109/3/5/3089 conserved, no native Lean refinement or D_N/WIN.'
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
for actor in cp['in_flight_executors']:
    if actor['role'] == 3: actor['status'] = 'NUMERIC05_CLOSED_NO_RETRY'
cp_path.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
with (B / 'REPORT.md').open('a',encoding='utf-8') as f: f.write('\n'+cp['last_progress']+'\n')
print(json.dumps(o,ensure_ascii=False,indent=2))
