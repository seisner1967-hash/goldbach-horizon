"""Bind explicit FINAL15 evidence only; no bank, compiler or Judge reexecution."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from pathlib import Path
from hashlib import sha256
from datetime import datetime, timezone
import json

BASE = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
RND = BASE / 'round15'
JUDGE = RND / 'judge'
def sha(path): return sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_bytes())
assert len(sys.argv) == 3, 'Explicit FINAL Judge report and receipt SHA required'
report_sha, receipt_sha = sys.argv[1:]
assert sha(RND / 'agent5.md') == report_sha
assert sha(JUDGE / 'judge_receipt.json') == receipt_sha
receipt = read(JUDGE / 'judge_receipt.json')
assert receipt['status'] == 'PARTIAL_SHORT_CONDUCTOR_COVARIANCE_AND_UNESTIMATED_ORPHAN_INCIDENCE'
assert receipt['score'] == 0 and receipt['victory'] is False
assert receipt['lean_invoked'] is False and receipt['compiler_failure_fabricated'] is False
assert receipt['new_lean_modules'] == receipt['new_lean_conclusions'] == 0
assert receipt['cumulative_auxiliary_modules'] == 15 and receipt['cumulative_auxiliary_conclusions'] == 208
for key in ('old_banks_rerun', 'new_producers_repeated_by_judge', 'old_lean_rerun',
            'old_pdf_rerendered', 'finite_witness_is_source_onset_test', 'global_no_go'):
    assert receipt[key] is False, key
assert receipt['preservation_before'] == receipt['preservation_after']
assert receipt['preservation_after']['files'] == 651
assert receipt['falsifier_count'] == len(receipt['falsifiers']) == 4
assert receipt['rational_sign_count'] == len(receipt['rational_signs']) == 1138
assert receipt['strict_signs'] and receipt['unresolved_signs'] == receipt['floating_values'] == 0
assert receipt['actual_numerical_failures'] == []

inputs = read(JUDGE / 'input_sha256.json')
assert sha(JUDGE / 'input_sha256.json') == receipt['input_manifest_sha256']
assert inputs['sha256'] == receipt['input_sha256']
assert inputs['file_count'] == len(inputs['sha256']) and len(inputs['reports']) == 3
assert all(v['terminated'] for v in inputs['final_role_signals'].values())
for name, digest in inputs['sha256'].items(): assert sha(RND / name) == digest, name
for name, digest in inputs['external_sha256'].items(): assert sha(Path(name)) == digest, name
for name, digest in receipt['judge_scripts_sha256'].items(): assert sha(JUDGE / name) == digest, name

expected = {
    'agent1_weighted_incidence.md': '8fa44b44dbb2c14fd4a5319840e26a4dc8d113d2db3c6b57dec5569e790bbf5d',
    'agent2_signed_cofactors.md': 'afe8511ce670dce4580837f444041159055addde605675cde328ba49a15f1fe7',
    'agent6.md': '3fd535fbbac417887f78f853cde9633adfeeb4e0a8c8fa72899ab1a75002257e',
    'numeric_manifest.json': 'a0563d33264e812c90aee4f457eab4afcbeb5a372261662cefe3b81ab63aeae8',
    'role6_final_receipt.json': '280ca5fbe0a289429fbce9ef7850319768ef7cffd81f0e0c7cb3b913c25a89d9',
    'previous_artifacts_sha256.json': 'd43941b27a4325a841282d389476c9c6fa9af920138b9b0deebe1c484a4ff7f4',
}
for name, digest in expected.items(): assert sha(RND / name) == digest, name
registry = read(RND / 'previous_artifacts_sha256.json')
assert registry['file_count'] == len(registry['sha256']) == 651
for name, digest in registry['sha256'].items(): assert sha(BASE / name) == digest, name
numeric = read(RND / 'numeric_manifest.json')
assert numeric['status'] == 'FINAL_FROZEN_NEW_ROUND15_NUMERIC_PARTIAL'
assert numeric['files'] == len(numeric['sha256']) == receipt['numeric_bindings'] == 35
for name, digest in numeric['sha256'].items(): assert sha(RND / name) == digest, name
for name, digest in numeric['reports_FINAL_sha256'].items(): assert sha(RND / name) == digest, name
counts = numeric['counting']
assert counts['new_banks'] == 2 and counts['necessary_read_only_supplements'] == 1
assert counts['canonical_attempts'] == counts['isolated_replays'] == 3
assert counts['real_failed_attempts'] == counts['old_PASS_replays'] == counts['new_Lean_modules'] == 0
for name in ('incidence', 'fusion', 'incidence_moment'):
    audit = receipt['bank_audits'][name]
    assert audit['all_fields_equal'] and audit['all_bytes_equal']
    assert audit['producer_invoked_by_judge'] is False
    assert sha(RND / (name + '.json')) == audit['receipt_sha256']
    assert sha(RND / ('isolated_' + name) / (name + '.json')) == audit['isolated_receipt_sha256']
    assert sha(RND / (name + '_checks.py')) == audit['source_sha256']
incidence, fusion = receipt['incidence'], receipt['fusion']
assert incidence['structural_mask'] == 4201 and incidence['first_prime_axes'] == 60982
assert incidence['first_prime_images'] == 912 and incidence['covariance_sign'] == 'NEGATIVE'
assert incidence['raw_unit_properpowers'] == 49 and incidence['raw_masked_properpowers'] == 4
assert incidence['all_kernels_exhaustively_evaluated'] is False
assert incidence['covariance_analytic_bound_obtained'] is False
assert fusion['q_primes'] == 21 and fusion['structural_labels'] == 86 and fusion['distinct_parent_cores'] == 78
assert fusion['candidate_vertices'] == 1680 and fusion['computed_D_W_profiles'] == 416
assert fusion['first_prime_parents'] == 360 and fusion['first_prime_targets'] == 7 and fusion['physical_edges'] == 112
assert fusion['orphan_targets'] == [] and fusion['principal_sign'] == fusion['actual_sign'] == 'NEGATIVE'
assert fusion['global_union_over_other_E_estimated'] is False
moment = read(RND / 'incidence_moment.json')
assert moment['Cauchy_L4']['strict_positive_gap_certified']
assert moment['AP_front']['X_exact'] == 97999795 and moment['AP_front']['front_difference_exact'] == '-35/23'
assert moment['producer_incidence_not_executed'] and moment['D_W_kernels_not_recomputed']

launch_path = JUDGE / 'audit_launch_receipt.json'
launch = read(launch_path)
assert launch['exit_code'] == 0
assert launch['status'] == 'OBSERVED_SINGLE_READ_ONLY_AUDIT_EXIT_ZERO' and launch['invocations'] == 1
assert launch['audit_reexecuted_for_logging'] is False
assert launch['Lean_invoked'] is False and launch['producer_executed_by_judge'] is False
assert launch['stdout_and_stderr_captured_from_original_launch']
assert sha(JUDGE / 'audit_launch.log') == launch['bindings_sha256']['audit_launch.log']
for name, digest in launch['bindings_sha256'].items(): assert sha(JUDGE / name) == digest, name
assert 'Score: 0' in (JUDGE / 'audit_launch.log').read_text(encoding='utf-8')
bindings = {p.relative_to(RND).as_posix(): sha(p) for p in sorted(RND.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts and p.name != 'controller_manifest.json'}
assert not any(n.endswith('.lean') for n in bindings)
manifest = dict(
    round=15, status=receipt['status'], recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    research_goal_active=True, objective_complete=False, victory=False, score=0,
    lean_invoked=False, new_lean_modules=0, new_lean_conclusions=0,
    cumulative_auxiliary_modules=15, cumulative_auxiliary_conclusions=208,
    previous_artifacts_preserved=651, round14_artifacts_preserved=48,
    frozen_input_bindings_verified=inputs['file_count'], numeric_bindings_verified=35,
    isolated_output_hashes_verified=3, new_candidate_banks=2, necessary_read_only_supplements=1,
    independent_judge_mode='readonly frozen inputs, three full isolated copies and stored vector audit',
    no_test_reexecution_by_controller=True, local_falsifiers=4,
    strict_rational_sign_positions=receipt['rational_sign_count'],
    actual_failed_numeric_attempts=[], actual_failed_lean_attempts=[],
    finite_N=100000000, source_adaptive_onset='u>=10^24', finite_witness_is_source_onset_test=False,
    global_impossibility_inferred=False,
    retained_ledger='D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',
    partial_mechanism='canonical short-conductor semiprime mask, centered covariance and signed small-core fusion with orphan selector',
    weighted_covariance_not_estimated=True, source_orphan_incidence_not_estimated=True,
    global_parent_reuse_not_paid=True, incidence=incidence, fusion=fusion,
    unpaid=receipt['semantic_open_obligations'], judge_report_sha256=report_sha,
    judge_receipt_sha256=receipt_sha, bindings_sha256=bindings,
    judge_launch_receipt_sha256=sha(launch_path), original_sources_sha256=inputs['external_sha256'])
dest = RND / 'controller_manifest.json'
assert not dest.exists(), 'FINAL15 controller already frozen'
dest.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=manifest['status'], files_bound=len(bindings), previous_verified=651,
    next_protected_expected=651 + len(bindings) + 1, retained_conclusions=208, victory=False,
    controller_sha256=sha(dest)), ensure_ascii=False))
