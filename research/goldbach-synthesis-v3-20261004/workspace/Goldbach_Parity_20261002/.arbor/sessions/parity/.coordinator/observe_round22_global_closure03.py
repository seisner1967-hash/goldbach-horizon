"""ROOT byte/receipt verification only; never recompute a numerical enclosure."""
import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role3/performance_sourcepack02/launch_prepare03'
A = P / 'actual_attempt01'
OLD = B / 'round22/role4/h1_global_numeric/launch_prepare02/actual_attempt01'

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
    return digest.hexdigest()

parser = argparse.ArgumentParser()
parser.add_argument('--receipt-sha', required=True)
parser.add_argument('--ROOT-full-read-receipts', required=True)
args = parser.parse_args()
assert sha(A / 'receipt.json') == args.receipt_sha
r = read(A / 'receipt.json')
assert r == read(A / 'FIN.json')
assert sha(A / 'FIN.json') == args.receipt_sha
assert r['status'] == 'THERMAL_TRACE_NUMERICAL_AUX_PASS_SOURCE_AUDITED'
assert r['child_exit_code'] == 0 and r['control_error'] is None and r['resource_failure'] is None
assert r['mathematical_children_started'] == 1
assert r['retries'] == r['old_bank_replays'] == r['Lean_invocations'] == 0
assert r['post_integrity'] and r['closed_attempt_integrity'] and not r['output_errors']
assert r['formal_H1'] == r['coefficient_N'] == 'OPEN' and r['D_N'] == 'UNPAID' and not r['WIN']
assert r['horizontal_volet'] == 'UNIMPLEMENTED'
assert not r['structural_PASS_is_enclosure_PASS'] and not r['structural_checker_alone_is_primitive_certificate']
assert r['future_evaluation_level'] == 'PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER'
assert r['analytic_certification_level'] == 'PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION'
assert r['resource_limits']['max_wall_seconds'] == 10800
assert r['resource_limits']['max_artifact_bytes'] == 2147483648
assert r['artifact_bytes_observed'] <= r['resource_limits']['max_artifact_bytes']
assert r['preparation_sha256'] == sha(P / 'preparation22.json') == '8d08bc4db8f702a53ae3340a2ba9102969caf7ea7995aa282638cd0e84919433'
assert r['independent_review_receipt_sha256'] == '638b1aaba849473a1806fe3b4bb967265b35f2ecb901b4003c0b661b114a1ddf'
assert r['independent_review_report_sha256'] == 'dfdc7d3a573c9d31364e198b8db749216316bec2162b19f4533babc1d2005286'
assert r['independent_domain_addendum_sha256'] == '821d67b2f8448533d707e9e23a5c33c44c4b316b297bb7f8129ac8f7d89cb4b7'
prep = read(P / 'preparation22.json')
gate = C / 'messages/round22_global_thermal_h1_authorization02.json'
assert r['root_gate_sha256'] == sha(gate) == '6847fff85e007303594f3257f2a027a7a4ccfb31393674338ebae22307f7a5c9'
pre, post = read(A / 'PREEXEC.json'), read(A / 'POSTEXEC.json')
start, child_start, child_fin = (read(A / filename) for filename in ('START.json', 'child_START.json', 'child_FIN.json'))
assert pre['token'] == start['token'] == child_start['token'] == child_fin['token'] == r['token'] == 'b104f84087a84a55a8ebfccdf5558a21'
assert start['time_utc'] == r['actual_START'] and start['PREEXEC_complete'] and start['no_retry']
assert start['context_sha256'] == pre['context_sha256'] == child_fin['context_sha256'] == sha(A / 'child_context.json')
assert post['all_intact'] and post['preparation_intact'] and post['root_gate_intact'] and post['context_intact']
assert post['closed_attempt']['unchanged'] and post['archive_error'] is None and post['closed_attempt_error'] is None
assert len(prep['bindings']) == len(pre['bindings']) == len(post['bindings']) == 1016
assert len(pre['captures']) == len(post['captures']) == 1018 and pre['all_captures_verified']
assert sum(row.get('source_packet') is True for row in prep['bindings']) == 21
expected = {row['path']: row for row in prep['bindings']}
for rows in (pre['bindings'], post['bindings']):
    assert set(expected) == {row['path'] for row in rows}
    for row in rows:
        item = expected[row['path']]
        assert row['unchanged'] and row['actual_sha256'] == row['expected_sha256'] == item['sha256'] == sha(Path(row['path']))
        assert Path(row['path']).stat().st_size == row['bytes'] == item['bytes']
post_captures = {row['path']: row for row in post['captures']}
assert set(post_captures) == {row['copy'] for row in pre['captures']}
for row in pre['captures']:
    item = post_captures[row['copy']]
    assert item['unchanged'] and sha(Path(row['copy'])) == sha(Path(row['original'])) == row['sha256'] == item['actual_sha256'] == item['expected_sha256']
    assert Path(row['copy']).stat().st_size == row['bytes'] == item['bytes']
registry = B / 'round22/previous_artifacts_sha256.json'
assert sha(registry) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
archives = read(registry)
assert len(archives['sha256']) == archives['file_count'] == 3089
for relative, digest in archives['sha256'].items():
    path = (B / relative).resolve()
    assert path.is_relative_to(B.resolve()) and sha(path) == digest
for inventory in (pre['archives'], post['archives']):
    assert inventory['unchanged'] and inventory['file_count'] == 3089 and inventory['registry_sha256'] == sha(registry)
old_receipt = read(OLD / 'receipt.json')
assert sha(OLD / 'receipt.json') == '2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93'
assert sha(OLD / 'FIN.json') == '2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93'
assert sha(OLD / 'PREEXEC.json') == 'b3734e005f391ddeef49c2342a8775218640c2c0e42e9146077008bb47dda4e3'
assert sha(OLD / 'POSTEXEC.json') == '3465bc934e6cab3dd204c3d0f3a939704a392b0beac32f123b081f3c6199eacf'
assert old_receipt['resource_failure'] == 'MAX_WALL_SECONDS'
old_pre = read(OLD / 'PREEXEC.json')
assert len(old_pre['bindings']) == 1003 and len(old_pre['captures']) == 1005
for row in old_pre['bindings']:
    assert sha(Path(row['path'])) == row['expected_sha256']
for row in old_pre['captures']:
    assert sha(Path(row['copy'])) == sha(Path(row['original'])) == row['sha256']
for row in old_receipt['outputs']:
    assert sha(Path(row['path'])) == row['sha256'] and Path(row['path']).stat().st_size == row['bytes']
assert len(r['outputs']) == 7
for row in r['outputs']:
    path = Path(row['path']).resolve()
    assert path.is_relative_to(A.resolve()) and sha(path) == row['sha256'] and path.stat().st_size == row['bytes']
assert child_fin['status'] == 'NUMERICAL_AGREEMENT_PENDING_POSTCHECK' and child_fin['exit_code'] == 0
assert child_fin['actual_all_guard_checks'] and child_fin['structural_checker_PASS'] and child_fin['independent_enclosure_source_review_bound']
assert not child_fin['structural_PASS_is_enclosure_PASS'] and not child_fin['structural_checker_alone_is_primitive_certificate']
assert child_fin['future_evaluation_level'] == r['future_evaluation_level']
assert child_fin['analytic_certification_level'] == r['analytic_certification_level']
g = read(A / 'numeric_data/global_thermal_result.json')
s = read(A / 'numeric_data/structural_checker_result.json')
assert g['status'] == s['numerical_decision'] == 'THERMAL_TRACE_NUMERIC_AGREEMENT'
assert g['parameters'] == {'N': 100000000, 'Q': 1000000, 'R': 1000000, 'T': 100, 'X': 1000000, 'Y': 10000}
assert g['complete_vertical_nodes'] == 204800 and g['complete_arch_nodes'] == 12288
assert s['arithmetic_integers_verified'] == 999999 and s['functional_nodes_verified'] == 217088
assert g['performance_counts'] == {'f1_constructions': 1, 'gamma_value_only': 204800, 'half_log_two_pi_constructions': 1}
assert g['old_bank_replays'] == g['old_output_inputs'] == 0
assert g['H1_FORMAL'] == g['COEFFICIENT_N'] == g['FINITE_ZERO_TRACE'] == 'OPEN'
assert g['D_N'] == 'UNPAID' and g['CONTOUR_BOUNDARY'] == 'UNIMPLEMENTED' and not g['WIN']
assert s['structural_checker_PASS'] and s['performance_source_guards_verified'] and not s['primitives_recomputed']
assert all(not s[name] for name in ('H1_FORMAL', 'COEFFICIENT_N', 'D_N', 'WIN', 'analytic_remainders_formalized'))
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
official = cp['official_auxiliary_validation']
observation = dict(schema='ROUND22_ROOT_GLOBAL03_CLOSED_METADATA_OBSERVATION', time_utc=datetime.now(timezone.utc).isoformat(),
    status=r['status'], receipt_sha256=args.receipt_sha, actual_START=r['actual_START'], actual_FINISH=r['actual_FINISH'],
    child_process_FINISH=r['child_process_FINISH'], inputs_verified=1016, captures_verified=1018, archives_verified=3089,
    closed_bank02_inputs_verified=1003, closed_bank02_captures_verified=1005, closed_bank02_outputs_verified=3,
    bound_output_count=7, outputs=r['outputs'], evaluation_level=r['future_evaluation_level'], analytic_level=r['analytic_certification_level'],
    numeric_guard_decision_owner='Actual ROLE6 child and source-reviewed structural checker; ROOT does not recompute numerical values',
    mathematical_error_and_mutant_audit_owner='ROLE6 with independent SOURCE/PAPER review; no ROOT mathematical audit',
    ROOT_full_read_receipts=args.ROOT_full_read_receipts, large_inventory_scope='All entries parsed and all bytes hash-verified; raw FULL node catalogs and global result text not claimed',
    official_modules=official['modules'], official_declarations=official['declarations'], official_credit_added=0,
    ROOT_numerical_invocations=0, ROOT_Lean_invocations=0, old_bank_replays=0, retries=0,
    H1_paid=False, coefficient_N_paid=False, D_N_paid=False, WIN=False)
output_path = C / 'messages/round22_global_closure03_observation.json'
with output_path.open('x', encoding='utf-8') as stream:
    json.dump(observation, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
insight = ('Banque thermique03 réellement close NUMERICAL_AUX_PASS_SOURCE_AUDITED, un enfant14:48:16–16:03:31UTC, '
    'FIN parent16:03:41, aucun retry/replay.204800 nœuds verticaux,12288 Arch,999999 entiers effectivement traités ; '
    '1016 bindings/1018 captures/3089 archives et ancien banc02 conservés. Gardes et comparaison déclarées validées par '
    'le producteur audité SOURCE/PAPIER et checker structurel, qui ne recalcule pas les primitives. Aucun nouveau crédit '
    'Lean ni H1 formel, trace de zéros complète, coefficient additifN, D_N ou WIN. Projection/NTT/PP/frontière restent ouverts.')
helper = r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
for command, extra in [('record', ['--node-id', '15.3', '--raw-report', insight, '--score', '0', '--insight', insight,
    '--result', 'NUMERICAL_AUX_SOURCE_AUDITED_GLOBAL_TARGET_OPEN', '--no-propagate']),
    ('update', ['--node-id', '15.3', '--status', 'running', '--insight', insight])]:
    result = subprocess.run([sys.executable, '-B', '-X', 'utf8', helper, command, '--cwd', str(B), '--run-name', 'parity', *extra], capture_output=True, text=True, encoding='utf-8')
    assert result.returncode == 0, (result.stdout, result.stderr)
cp['phase'] = 'ROUND22_GLOBAL_NUMERIC03_AUX_PASS_IDENTITY_FORMAL_CONTINUATION'
cp['last_progress'] = insight
cp['previous_goal_turn_evidence'].append(str(output_path.relative_to(B)))
for actor in cp['in_flight_executors']:
    if actor['role'] == 3:
        actor['status'] = 'ROLE6_GLOBAL03_CLOSED_AUX_SOURCE_AUDITED_AND_ROLE3_MELLIN_SOURCE'
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as stream:
    stream.write('\n' + insight + '\n')
print(json.dumps(observation, ensure_ascii=False, indent=2))
