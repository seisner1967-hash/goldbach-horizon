"""ROOT observes closed ROLE6 receipts and byte conservation; no numeric evaluation."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role3/native_numeric_consumer_source01'
A = P / 'actual_numeric04_attempt01'
gate_path = C / 'messages/round22_native_numeric04_authorization.json'

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def check(p, digest, size=None):
    assert p.is_file() and sha(p) == digest, str(p)
    assert size is None or p.stat().st_size == size, str(p)

parser = argparse.ArgumentParser()
for name in ('receipt-sha', 'closure-path', 'closure-sha', 'ROOT-full-reads'):
    parser.add_argument('--' + name, required=True)
args = parser.parse_args()
closure_path = Path(args.closure_path)
assert closure_path.resolve().is_relative_to(B.resolve())
check(closure_path, args.closure_sha)
check(A / 'receipt.json', args.receipt_sha)
closure, receipt, gate, pre, post = [read(p) for p in
    (closure_path, A / 'receipt.json', gate_path, A / 'PRE.json', A / 'POST.json')]
assert closure['actual_parent_receipt_sha256'] == args.receipt_sha
assert closure['parent_invocations'] == 1 and closure['retry_count'] == 0
assert closure['all_current_bytes_preserved'] is True
assert closure['actual_processes_quiescent'] is True
assert receipt['parent_invocations'] == 1 and receipt['retry_count'] == 0
assert receipt['scope'] == gate['scope'] == 'NATIVE_NUMERIC04_FULL_N1E8_ONLY'
assert receipt['gate_sha256'] == pre['gate_sha256'] == sha(gate_path)
assert receipt['preparation_sha256'] == pre['preparation_sha256'] == sha(P / 'numeric_preparation22.json')
assert receipt['conservation_error'] is None
assert post['conservation_error'] is None and post['all_bindings_controls_originals_copies_archives_intact'] is True
assert receipt['compiler_invocations'] == 0 and receipt['mutant_runs'] == 0
for flag in ('native_Lean_refinement', 'B40_real_log_refinement_Lean', 'spectral_H1', 'D_N', 'WIN',
             'effective_loads_observed', 'universal_loader_closure_verified'):
    assert receipt[flag] is False
assert receipt['limits'] == {k: gate[k] for k in receipt['limits']}
assert receipt['children_returned'] == len(receipt['results']) <= 2
assert 0 <= receipt['produced_binary_processes_resumed'] <= receipt['produced_binary_processes_created'] <= 2
assert receipt['binary_sha256'] == gate['binary_sha256']
rows = read(P / 'numeric_manifest22.json')['bindings']
assert len(rows) == gate['inputs_verified'] == pre['binding_count'] == 6456
for row in rows:
    check(Path(row['path']), row['sha256'], row['bytes'])
for row in pre['captures']:
    check(Path(row['original']), row['sha256'])
    check(Path(row['copy']), row['sha256'])
for row in gate['metadata_control_bindings']:
    check(Path(row['path']), row['sha256'])
for row in closure['output_bindings']:
    check(Path(row['path']), row['sha256'], row['bytes'])
registry_path = B / 'round22/previous_artifacts_sha256.json'
check(registry_path, '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99')
registry = read(registry_path)['sha256']
assert len(registry) == 3089
for relative, digest in registry.items():
    path = (B / relative).resolve()
    assert path.is_relative_to(B.resolve())
    check(path, digest)
success_status = 'PAPER_AUDITED_EXACT_INTEGER_PROJECTION_AUX_CHECKED_PENDING_NATIVE_REFINEMENT'
success = receipt['status'] == success_status
if success:
    assert receipt['failure'] is None and receipt['children_returned'] == 2
    assert receipt['produced_binary_processes_created'] == receipt['produced_binary_processes_resumed'] == 2
    assert receipt['coefficient_result_present'] is True
    assert all(row['exit_code'] == 0 and row['job_empty_confirmed'] is True for row in receipt['results'])
    result = read(A / 'coefficient_result.json')
    for flag in ('native_Lean_refinement', 'B40_real_log_refinement_Lean', 'spectral_H1', 'D_N', 'WIN'):
        assert result[flag] is False
    assert result['interval_link_level'] == 'PAPER_AUDITED_PENDING_NATIVE_CATALOGUE_AND_MACHINE_REFINEMENT'
else:
    assert receipt['status'] == 'NATIVE_NUMERIC_STOP_NO_MATHEMATICAL_VERDICT'
    assert receipt['coefficient_result_present'] is False
    assert not (A / 'coefficient_result.json').exists()
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
official = cp['official_auxiliary_validation']
observation = dict(schema='ROUND22_ROOT_NATIVE_NUMERIC04_CLOSED_OBSERVATION',
    utc=datetime.now(timezone.utc).isoformat(), actual_status=receipt['status'],
    parent_invocations=1, retry_count=0, child_created=receipt['produced_binary_processes_created'],
    child_resumed=receipt['produced_binary_processes_resumed'], child_returned=receipt['children_returned'],
    actual_parent_failure=receipt['failure'], coefficient_result_present=success,
    numerical_verdict_level='PAPER_AUX_PENDING_NATIVE_REFINEMENT' if success else 'STOP_NO_MATHEMATICAL_VERDICT',
    actual_receipt_sha256=args.receipt_sha, closure_path=str(closure_path), closure_sha256=args.closure_sha,
    ROOT_full_reads=args.ROOT_full_reads, inputs_verified=len(rows), captures_verified=len(pre['captures']),
    archives_verified=3089, output_bindings_verified=len(closure['output_bindings']),
    all_current_bytes_preserved=True, actual_processes_quiescent=True,
    official_modules=official['modules'], official_declarations=official['declarations'],
    Lean_credit_from_numerical_attempt=0, ROOT_compiler_invocations=0, ROOT_numeric_invocations=0,
    native_Lean_refinement=False, spectral_H1=False, D_N=False, WIN=False)
out = C / 'messages/round22_native_numeric04_closed_observation.json'
with out.open('x', encoding='utf-8') as f:
    json.dump(observation, f, ensure_ascii=False, indent=2)
    f.write('\n')
cp['phase'] = 'ROUND22_NATIVE_NUMERIC04_CLOSED_GLOBAL_ANALYTIC_OBLIGATIONS_OPEN'
cp['last_progress'] = receipt['status'] + '; no D_N/WIN or machine-refinement proof.'
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as f:
    f.write('\nROUND22 actual numeric04: ' + receipt['status'] + '; ' + str(out.relative_to(B)) +
            '; unchanged auxiliary Lean credit, global D_N/WIN OPEN.\n')
print(json.dumps(observation, ensure_ascii=False, indent=2))
