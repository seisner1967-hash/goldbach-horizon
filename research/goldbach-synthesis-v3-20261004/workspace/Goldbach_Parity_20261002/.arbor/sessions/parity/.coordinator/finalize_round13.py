"""Bind FINAL13 evidence only; execute no numerical producer or Lean compiler."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
from pathlib import Path
from datetime import datetime, timezone

BASE = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
RND = BASE / 'round13'
JUDGE = RND / 'judge'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_bytes())
assert len(sys.argv) == 3, 'Announced FINAL Judge report and receipt SHA required'
report_sha, receipt_sha = sys.argv[1:]
assert sha(RND / 'agent5.md') == report_sha
assert sha(JUDGE / 'judge_receipt.json') == receipt_sha
receipt = read(JUDGE / 'judge_receipt.json')
assert receipt['status'] == 'PARTIAL_ACTUAL_PRIME_SEMIPRIME_SWITCH_WITH_UNPAID_COMPLEMENT'
assert receipt['score'] == 0 and receipt['victory'] is False
assert receipt['lean_invoked'] and not receipt['custom_oleans_reused']
assert receipt['new_lean_modules'] == 2 and receipt['new_lean_conclusions'] == 39
assert receipt['new_definition_count'] == 5
assert receipt['cumulative_auxiliary_modules'] == 15
assert receipt['cumulative_auxiliary_conclusions'] == 208
assert receipt['old_banks_rerun'] is False
assert receipt['old_independent_modules_rerun'] is False
assert receipt['required_old_dependencies_rebuilt'] is True
assert receipt['global_no_go'] is False
assert receipt['preservation_before'] == receipt['preservation_after']
assert receipt['preservation_after']['files'] == 514
assert receipt['preservation_after']['round12_files'] == 27
payment = receipt['written_switch_payment']
assert payment['amount'] == '21*N^(31/32)*u^2'
assert payment['written_not_compiler_certified'] and payment['paired_fee_only']
assert payment['unmatched_not_assumed_small'] and payment['P5_full_bulk_J2_preserved']
inputs_path = JUDGE / 'input_sha256.json'
inputs = read(inputs_path)
assert sha(inputs_path) == receipt['input_manifest_sha256']
assert inputs['sha256'] == receipt['input_sha256']
assert inputs['file_count'] == len(inputs['sha256']) == 64
assert len(inputs['reports']) == 5
assert all(v['terminated'] for v in inputs['final_role_signals'].values())
for name, digest in inputs['sha256'].items(): assert sha(RND / name) == digest, name
for name, digest in inputs['external_sha256'].items(): assert sha(Path(name)) == digest, name
for name, digest in receipt['judge_scripts_sha256'].items(): assert sha(JUDGE / name) == digest, name
expected = {
    'agent1_exchange.md': '2b64a5434c1dfde766436d5abd44b62a2714615992193a3f0e21bf90554d8c54',
    'agent2_signed_operator.md': '91946283d4ca1f5021de670b16167e0a0714d0945104d30c4070ca9a26bc9c46',
    'agent3_formalisation.md': '7fc3187840c63090bbdd180e6fe877f2c16f889022a9a7505a52673acc49f3b0',
    'agent4_formalisation.md': '8989da2b8610afdf237ecc7292d82522c2543b3520fd0871aa726d17a2a2e813',
    'agent6.md': '00e234c7543fbb77d41f3f7d297c15b6bb649b6d940179509f7d916e68bb6bc0',
    'role3_final_receipt.json': '4c56ef717bf7e9b75f6463d33259b385ead05ac66e38067a8930a359baf7caf2',
    'role4_final_receipt.json': '59f2ed42f942d5daaf3c7b7d4d843eb26ae783de4d493c5f656ab504dbf6111c',
    'lean/PrimeSemiprimeSwitch.lean': '21462365bb2fe343015161fc67639ed7bbba1234cfbbd985c90bb3d591a84da4',
    'lean/HarmonicKernelVariation.lean': '7bc1ee92e0e9c6000fd31afdc05a0a827a254d60354d6519c145727e886b1e95',
    'numeric_manifest.json': 'c8468f94a118555c842a47879772620bf9dca9d520a6b89cec54f2895a38f932',
    'previous_artifacts_sha256.json': '02c04c95e5348369b9c4577ac3a14e5b4b89e15f53e142e75a37e58b6bde7351',
}
for name, digest in expected.items(): assert sha(RND / name) == digest, name
registry = read(RND / 'previous_artifacts_sha256.json')
assert registry['file_count'] == len(registry['sha256']) == 514
for name, digest in registry['sha256'].items(): assert sha(BASE / name) == digest, name
numeric = read(RND / 'numeric_manifest.json')
assert numeric['file_count'] == len(numeric['sha256']) == 11
for name, digest in numeric['sha256'].items(): assert sha(RND / name) == digest, name
audit = receipt['numerical_audit']
assert audit['falsifier_count'] == 8 and audit['rational_sign_count'] == 17
assert audit['strict_signs'] and audit['floating_values'] == 0
assert audit['producer_repeated_by_judge'] is False
assert audit['analytic_payment_tested'] is False and audit['source_onset_tested'] is False
assert sha(JUDGE / 'numerical_audit_receipt.json') == receipt['numerical_audit_receipt_sha256']
assert read(JUDGE / 'numerical_audit_receipt.json') == audit
assert len(audit['banks']) == 2
for name, row in audit['banks'].items():
    assert row['all_fields_equal'] and row['all_bytes_equal']
    assert row['producer_executed_by_judge'] is False
    assert sha(RND / name) == row['receipt_sha256']
    assert sha(RND / 'isolated_output_probe' / name) == row['receipt_sha256']
    assert (RND / name).read_bytes() == (RND / 'isolated_output_probe' / name).read_bytes()
    assert read(RND / name) == read(RND / 'isolated_output_probe' / name)
proofs, new_proofs = [], []
for entry in receipt['dependency_rebuilds'] + receipt['modules']:
    assert entry['exit_code'] == 0 and entry['status'] == 'PASS_FRESH_COMPILE_STANDARD_AXIOMS'
    assert not entry['warnings'] and not entry['forbidden_executable_tokens']
    for key in ('instrumented_source', 'log', 'olean'):
        assert sha(Path(entry[key])) == entry[key + '_sha256'], entry['module']
    snapshot = Path(entry['source_snapshot'])
    assert sha(snapshot) == entry['original_source_sha256']
    assert Path(entry['instrumented_source']).read_text(encoding='utf-8').startswith(snapshot.read_text(encoding='utf-8'))
    assert set(entry['theorem_names']) == set(entry['theorem_axioms'])
    assert set(entry['definition_names']) == set(entry['definition_axioms'])
    assert len(entry['theorem_names']) == entry['theorem_count']
    for group in ('theorem_axioms', 'definition_axioms', 'other_printed_axioms'):
        assert all(set(v) <= STANDARD for v in entry[group].values())
    proofs.extend(entry['theorem_names'])
    if entry['new_module']: new_proofs.extend(entry['theorem_names'])
assert len(proofs) == 75 and len(new_proofs) == len(set(new_proofs)) == 39
for filename, key in [('role3_final_receipt.json', 'owned_artifacts_sha256'), ('role4_final_receipt.json', 'sha256')]:
    for name, digest in read(RND / filename)[key].items(): assert sha(RND / name) == digest, name
bindings = {p.relative_to(RND).as_posix(): sha(p) for p in sorted(RND.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts and p.name != 'controller_manifest.json'}
manifest = dict(round=13, status=receipt['status'], recorded_at_utc=datetime.now(timezone.utc).isoformat(),
    research_goal_active=True, objective_complete=False, victory=False, score=0,
    lean_invoked=True, new_lean_modules=2, new_lean_conclusions=39, new_definitions=5,
    cumulative_auxiliary_modules=15, cumulative_auxiliary_conclusions=208,
    previous_artifacts_preserved=514, round12_artifacts_preserved=27,
    frozen_input_bindings_verified=64, numeric_bindings_verified=11, isolated_output_hashes_verified=2,
    independent_judge_mode='readonly frozen replay audit then necessary fresh source compilation',
    no_test_reexecution_by_controller=True, local_falsifiers=8, strict_rational_sign_positions=17,
    actual_failed_lean_attempts={'role3': [1, 2, 4], 'role4': [1]},
    finite_N=100000000, source_adaptive_onset='u>=10^24', finite_witness_is_source_onset_test=False,
    global_impossibility_inferred=False,
    retained_ledger='D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',
    partial_mechanism='actual downward prime/semiprime crossing, canonical parent and image, disjoint supports',
    finite_kernel_variation_compiled=True, written_switch_payment=payment,
    unmatched_coverage_not_estimated=True, unpaid=receipt['semantic_open_obligations'],
    judge_report_sha256=report_sha, judge_receipt_sha256=receipt_sha,
    bindings_sha256=bindings, original_sources_sha256=inputs['external_sha256'])
dest = RND / 'controller_manifest.json'
dest.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=manifest['status'], files_bound=len(bindings), previous_verified=514,
    new_lean_conclusions=39, retained_conclusions=208, victory=False, controller_sha256=sha(dest)), ensure_ascii=False))
