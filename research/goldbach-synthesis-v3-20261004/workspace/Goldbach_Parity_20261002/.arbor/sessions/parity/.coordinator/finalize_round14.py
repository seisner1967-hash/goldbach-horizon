"""Bind FINAL14 evidence only; do not run a producer or Lean compiler."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
import hashlib
import json
from pathlib import Path
from datetime import datetime, timezone

BASE = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
RND = BASE / 'round14'
JUDGE = RND / 'judge'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_bytes())
assert len(sys.argv) == 3, 'Explicit FINAL Judge report and receipt SHA required'
report_sha, receipt_sha = sys.argv[1:]
assert sha(RND / 'agent5.md') == report_sha
assert sha(JUDGE / 'judge_receipt.json') == receipt_sha
receipt = read(JUDGE / 'judge_receipt.json')
assert receipt['status'] == 'PARTIAL_EXACT_CAPACITY_DEFECT_WITH_UNESTIMATED_INTERIOR'
assert receipt['score'] == 0 and receipt['victory'] is False
assert receipt['lean_invoked'] is False and receipt['compiler_failure_fabricated'] is False
assert receipt['new_lean_modules'] == receipt['new_lean_conclusions'] == 0
assert receipt['cumulative_auxiliary_modules'] == 15
assert receipt['cumulative_auxiliary_conclusions'] == 208
for key in ('old_banks_rerun', 'new_producers_repeated_by_judge',
            'supplement_repeated_by_judge', 'old_lean_rerun', 'old_pdf_rerendered',
            'finite_witness_is_source_onset_test', 'global_no_go'):
    assert receipt[key] is False, key
assert receipt['preservation_before'] == receipt['preservation_after']
assert receipt['preservation_after']['files'] == 603
assert receipt['falsifier_count'] == len(receipt['falsifiers']) == 4
assert receipt['rational_sign_count'] == len(receipt['rational_signs']) == 27
assert receipt['strict_signs'] and receipt['unresolved_signs'] == receipt['floating_values'] == 0
assert receipt['supplemental_unique_pairs'] == 7
assert receipt['supplemental_actual_sign_counts'] == {'POSITIVE': 6, 'NEGATIVE': 1, 'ZERO': 0}
assert receipt['distinct_actual_vertices_checked'] == 78
assert receipt['complement_all_descent_C4_edges_checked'] == 44
inputs = read(JUDGE / 'input_sha256.json')
assert sha(JUDGE / 'input_sha256.json') == receipt['input_manifest_sha256']
assert inputs['sha256'] == receipt['input_sha256']
assert inputs['file_count'] == len(inputs['sha256']) == 37
assert len(inputs['reports']) == 3
assert all(v['terminated'] for v in inputs['final_role_signals'].values())
for name, digest in inputs['sha256'].items(): assert sha(RND / name) == digest, name
for name, digest in inputs['external_sha256'].items(): assert sha(Path(name)) == digest, name
for name, digest in receipt['judge_scripts_sha256'].items(): assert sha(JUDGE / name) == digest, name
launch = read(JUDGE / 'audit_launch_receipt.json')
assert launch['status'] == 'RECORDED_ACTUAL_COMPLETED_AUDIT_NO_RERUN'
assert launch['exit_code'] == 0 and launch['audit_reexecuted_for_recording'] is False
assert launch['lean_invoked'] is False and launch['numerical_producer_invoked'] is False
assert sha(JUDGE / 'audit_launch.log') == launch['stdout_sha256']
for name, digest in launch['bindings_sha256'].items(): assert sha(JUDGE / name) == digest, name
assert (JUDGE / 'audit_launch.log').read_text(encoding='utf-8').endswith('Score: 0\n')
expected = {
    'agent1_coverage.md': '4224fdd0f202da0a1dae1787965cb24aaeb7cf88fbcba8e92f607aff98716aec',
    'agent2_complement.md': 'b512cffb393253b004660442dd5cdde7af228d1550dbdc8c926d8e899c186d67',
    'agent6.md': '6a5020f476b597fc5b4b4482d71acb2612bca242384de905886d058680539b31',
    'numeric_manifest.json': 'fe73d3c34e07ce7ee1e38f436f23d4015f9c6485e3e852adbfb323e8baa87bcd',
    'role6_final_receipt.json': '0cb35796d1b790b46a27a193b2f79280015b1c1f59b0150801447c4240834b3d',
    'previous_artifacts_sha256.json': '310e5f7df62b7f67fa29302f2eb634a740da6f979ce8c23f0a4415941b075407',
}
for name, digest in expected.items(): assert sha(RND / name) == digest, name
registry = read(RND / 'previous_artifacts_sha256.json')
assert registry['file_count'] == len(registry['sha256']) == 603
for name, digest in registry['sha256'].items(): assert sha(BASE / name) == digest, name
numeric = read(RND / 'numeric_manifest.json')
assert numeric['file_count'] == len(numeric['sha256']) == receipt['numeric_bindings'] == 32
for name, digest in numeric['sha256'].items(): assert sha(RND / name) == digest, name
for name, digest in numeric['final_conceptual_report_sha256'].items(): assert sha(RND / name) == digest, name
for name in ('coverage', 'complement'):
    audit = receipt['bank_audits'][name]
    assert audit['all_fields_equal'] and audit['all_bytes_equal']
    assert audit['producer_invoked_by_judge'] is False
    assert sha(RND / (name + '.json')) == audit['receipt_sha256']
    assert sha(RND / ('isolated_' + name) / (name + '.json')) == audit['isolated_receipt_sha256']
    assert sha(RND / (name + '_checks.py')) == audit['source_sha256']
assert receipt['graphs']['graph_all']['prefix_deficit'] == 5
assert receipt['graphs']['graph_interior']['prefix_deficit'] == 4
for name, counts in (('C1', (10, 21)), ('C2', (1, 23))):
    cut = receipt['cuts'][name]
    assert (cut['parents'], cut['images']) == counts
    assert cut['debt'] == cut['capacity'] == 'POSITIVE' and cut['expanded_defect'] == 'NEGATIVE'
assert receipt['real_failed_numerical_selection']['exit_code'] == 1
assert receipt['real_failed_numerical_selection']['attempt'] == 1
costs = receipt['written_partial_costs']
assert costs['window_variation'] == '42*N^(63/64)*u^2'
assert costs['whole_front'] == '28*N^(37/64)*u^3*(1+u)'
assert costs['written_not_Lean_certified'] and costs['interior_capacity_not_paid']
assert costs['alternative_U4_not_double_counted']
bindings = {p.relative_to(RND).as_posix(): sha(p) for p in sorted(RND.rglob('*'))
    if p.is_file() and '__pycache__' not in p.parts and p.name != 'controller_manifest.json'}
assert not any(n.endswith('.lean') for n in bindings)
manifest = dict(round=14, status=receipt['status'], recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    research_goal_active=True, objective_complete=False, victory=False, score=0,
    lean_invoked=False, new_lean_modules=0, new_lean_conclusions=0,
    cumulative_auxiliary_modules=15, cumulative_auxiliary_conclusions=208,
    previous_artifacts_preserved=603, round13_artifacts_preserved=89,
    frozen_input_bindings_verified=37, numeric_bindings_verified=32, isolated_output_hashes_verified=2,
    root_preliminary_full_copy_and_field_comparison_passed=True,
    independent_judge_mode='readonly frozen inputs, full isolated copies and stored vector audit',
    no_test_reexecution_by_controller=True, local_falsifiers=4, strict_rational_sign_positions=27,
    actual_failed_numeric_attempts={'complement': [1]}, actual_failed_lean_attempts=[],
    finite_N=100000000, source_adaptive_onset='u>=10^24', finite_witness_is_source_onset_test=False,
    global_impossibility_inferred=False,
    retained_ledger='D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',
    partial_mechanism='normalized two-sided graph charge, nested-prefix matching, arithmetic CRT cuts and unique actual capacities',
    weighted_full_incidence_comparison_not_estimated=True, written_partial_costs=costs,
    unpaid=receipt['semantic_open_obligations'], judge_report_sha256=report_sha,
    judge_receipt_sha256=receipt_sha, bindings_sha256=bindings,
    judge_launch_receipt_sha256=sha(JUDGE / 'audit_launch_receipt.json'),
    original_sources_sha256=inputs['external_sha256'])
dest = RND / 'controller_manifest.json'
assert not dest.exists(), 'FINAL14 controller already frozen'
dest.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=manifest['status'], files_bound=len(bindings), previous_verified=603,
    new_lean_conclusions=0, retained_conclusions=208, victory=False, controller_sha256=sha(dest)), ensure_ascii=False))
