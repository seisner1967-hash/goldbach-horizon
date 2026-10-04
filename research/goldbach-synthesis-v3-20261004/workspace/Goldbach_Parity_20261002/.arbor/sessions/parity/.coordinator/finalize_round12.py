"""Bind final round12 evidence; execute no producer, arithmetic test, or Lean."""
import sys
sys.dont_write_bytecode = True
import json
import hashlib
from pathlib import Path
from datetime import datetime, timezone

BASE = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
RND = BASE / 'round12'
JUDGE = RND / 'juge'
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path): return json.loads(path.read_bytes())
assert len(sys.argv) == 3, 'Final Judge report and receipt SHA required'
report_sha, receipt_sha = sys.argv[1:]
assert sha(RND / 'agent5.md') == report_sha
assert sha(JUDGE / 'judge_receipt.json') == receipt_sha
receipt = read(JUDGE / 'judge_receipt.json')
assert receipt['status'] == 'REJECTED_BEFORE_LEAN_WITH_VALID_GUARDED_IDENTITIES'
assert receipt['score'] == 0 and receipt['victory'] is False
assert receipt['lean_invoked'] is False and receipt['compiler_failure_fabricated'] is False
assert receipt['new_lean_modules'] == receipt['new_lean_conclusions'] == 0
assert receipt['cumulative_auxiliary_modules'] == 13
assert receipt['cumulative_auxiliary_conclusions'] == 169
assert receipt['numerical_producers_invoked_by_judge'] is False
assert receipt['falsifier_count'] == 10 and receipt['rational_sign_count'] == 13
assert receipt['strict_signs'] is True and receipt['unresolved_signs'] == 0
assert receipt['preservation_before'] == receipt['preservation_after']
assert receipt['preservation_after']['files'] == 487
assert receipt['finite_witness_is_source_onset_test'] is False
assert receipt['global_no_go'] is False
inputs_path = JUDGE / 'input_sha256.json'
inputs = read(inputs_path)
assert sha(inputs_path) == receipt['input_manifest_sha256']
assert inputs['sha256'] == receipt['input_sha256']
assert inputs['file_count'] == len(inputs['sha256']) == 20
assert all(row['terminated'] for row in inputs['final_role_signals'].values())
for name, digest in inputs['sha256'].items():
    assert sha(RND / name) == digest, name
for name, digest in inputs['external_sha256'].items():
    assert sha(Path(name)) == digest, name
for name, digest in receipt['judge_scripts_sha256'].items():
    assert sha(JUDGE / name) == digest, name
expected = {
    'agent1_compensation.md': '896111f4bdc27e79ef352703be83f5b84e2bd26adb5c03644698fe06fcd5775c',
    'agent2_bilateral.md': '71e8b1fb2d7a4d20d146e4357ea0a6ab5f7c1fd0af77d1386db50dbaf5ecd91a',
    'agent6.md': 'ee2383547abc96817911f7120e09246a2d36e579e940004cd8d2062688198759',
    'numeric_manifest.json': 'e6c7321c0584827e72e1850f0053018b598e35229bc818affaf1b83462198592',
    'numerical_replay.json': '653b4089491e6f18050394e226208dcdd287c1e16e97adf64fe0b9f0b082bcc0',
    'previous_artifacts_sha256.json': '9a0a1010cdc4ad16eeb28b15f960f1d7dd3621bc91cc4d241a8781ccc2e543b1',
}
for name, digest in expected.items(): assert sha(RND / name) == digest, name
registry = read(RND / 'previous_artifacts_sha256.json')
assert registry['file_count'] == len(registry['sha256']) == 487
for name, digest in registry['sha256'].items(): assert sha(BASE / name) == digest, name
numeric = read(RND / 'numeric_manifest.json')
assert numeric['file_count'] == len(numeric['sha256']) == 13
for name, digest in numeric['sha256'].items(): assert sha(RND / name) == digest, name
for name, row in receipt['bank_audits'].items():
    assert row['all_fields_equal'] and row['all_bytes_equal']
    assert row['producer_executed_by_judge'] is False
    assert sha(RND / name) == row['receipt_sha256']
    assert sha(RND / 'isolated_output_probe' / name) == row['receipt_sha256']
bindings = {p.relative_to(RND).as_posix(): sha(p) for p in sorted(RND.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts and p.name != 'controller_manifest.json'}
assert not any(name.endswith(('.lean', '.olean')) for name in bindings)
manifest = dict(round=12, status=receipt['status'],
    recorded_at_utc=datetime.now(timezone.utc).isoformat(), research_goal_active=True,
    objective_complete=False, victory=False, score=0,
    lean_invoked=False, compiler_failure_fabricated=False,
    new_lean_modules=0, new_lean_conclusions=0,
    cumulative_auxiliary_modules=13, cumulative_auxiliary_conclusions=169,
    previous_artifacts_preserved=487, round11_artifacts_preserved=82,
    frozen_input_bindings_verified=20, numeric_bindings_verified=13,
    isolated_output_hashes_verified=3,
    independent_judge_mode=receipt['numerical_audit_mode'],
    no_test_reexecution_by_controller=True,
    local_falsifiers=10, strict_rational_sign_positions=13,
    finite_N=100000000, source_adaptive_onset='u>=10^24',
    finite_witness_is_source_onset_test=False, global_impossibility_inferred=False,
    retained_ledger='D_N=B_prime^a9+B_pp^a9+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',
    source54_literal_exponent='-sqrt(u/60)', weaker_majorant_used='-sqrt(u)/60',
    failed_promotions=[
        'Weighted Hall capacity in every closed bulk prime-deletion component: one whole finite star has positive demand minus capacity',
        'Free inverse-log saving after complete prime-factor coverage: absolute mass is exactly one',
        'Deletion identity with missing squarefree guard, missing log denominator or unweighted factors',
        'Short-cofactor truncation completed without retaining c>a',
        'Unit matching root density without unit guard',
        'Log-concavity for every selected parity polynomial',
        'Detector prime-power correction omitted'],
    valid_finite_identities_not_selected_as_bypass=[
        'Complete normalized prime-deletion transfer with actual Lambda_N, c=1 and long complement',
        'Guarded detector E=V-P with first-axis properpowers retained',
        'Exact matching finite root count and physical three-incidence star'],
    unpaid=receipt['semantic_open_obligations'],
    dispersion_not_refuted_but_unestimated=True,
    source_hashes_match_judge=True, announced_final_hashes_match=True,
    judge_report_sha256=report_sha, judge_receipt_sha256=receipt_sha,
    bindings_sha256=bindings, original_sources_sha256=inputs['external_sha256'])
dest = RND / 'controller_manifest.json'
dest.write_text(json.dumps(manifest, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
print(json.dumps(dict(status=manifest['status'], files_bound=len(bindings),
    protected_verified=487, new_lean_conclusions=0, retained_conclusions=169,
    victory=False, controller_sha256=sha(dest)), ensure_ascii=False))
