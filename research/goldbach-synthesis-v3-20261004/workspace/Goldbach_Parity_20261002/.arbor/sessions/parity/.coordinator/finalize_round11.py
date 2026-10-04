"""Bind final independent evidence; perform no mathematical test or compile."""
import sys
sys.dont_write_bytecode = True
import json, hashlib
from pathlib import Path
from datetime import datetime, timezone
base = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
rnd = base / 'round11'
judge = rnd / 'judge'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text(encoding='utf-8'))
assert len(sys.argv) == 3, 'Final Judge report and receipt SHA signals required'
report_sha, receipt_sha = sys.argv[1:]
assert sha(rnd/'agent5.md') == report_sha
assert sha(judge/'judge_receipt.json') == receipt_sha
receipt = read(judge/'judge_receipt.json')
assert receipt['victory'] is False and receipt['score'] == 0
assert receipt['new_lean_modules'] == 2 and receipt['new_lean_conclusions'] == 28
assert receipt['cumulative_auxiliary_modules'] == 13 and receipt['cumulative_auxiliary_conclusions'] == 169
assert receipt['production_sha256_before'] == receipt['production_sha256_after']
for absolute, digest in receipt['production_sha256_after'].items():
    assert sha(Path(absolute)) == digest, absolute
inputs = read(judge/'input_sha256.json')
assert sha(judge/'input_sha256.json') == receipt['input_manifest_sha256']
assert inputs['sha256'] == receipt['source_sha256']
for relative, digest in inputs['sha256'].items(): assert sha(rnd/relative) == digest, relative
for absolute, digest in inputs['external_sha256'].items(): assert sha(Path(absolute)) == digest, absolute
assert sha(rnd/'previous_artifacts_sha256.json') == 'f86a31f72d624124338afad6932cd859dceae164a6f3422f9b8998164fcf9e05'
registry = read(rnd/'previous_artifacts_sha256.json')
assert registry['file_count'] == len(registry['sha256']) == 405
for relative, digest in registry['sha256'].items(): assert sha(base/relative) == digest, relative
expected = {
'lean/SquarefreeLcmCoefficient.lean':'f791b4be0f731244a44449f27bb236c7890a8265c0e7fa6d55150a1a230e1ba6',
'agent3_formalisation.md':'a9b85fb0801736a7938575ef11719a1a9e4df5e0b67b0dcd706c725482f4127e',
'role3_final_receipt.json':'82cececd4e802ef0fe29af350a49ac541f17ec2ae1f615539bee225ea67da9d2',
'lean/ThreeAdicPrimePairing.lean':'b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48',
'agent4_formalisation.md':'8ee163dbacf009e4a60f6e38f4378df64ec6d6c0205057627e99cbdffb8ccedc',
'role4_build_receipt.json':'3c66240216e4e5b3e985632618a3f92233a1445a2d7ae6aa955c75fd61639a4a',
'agent5.md': report_sha, 'judge/judge_receipt.json': receipt_sha,
'numeric_manifest.json':'cf00e641312588a0ab8d9e410f005585bb3e00a0b30b8cee54ba0c1fe7a113c1'}
for relative, digest in expected.items(): assert sha(rnd/relative) == digest, relative
assert len(receipt['modules']) == 2 and len(receipt['dependency_rebuilds']) == 1
assert receipt['dependency_rebuilds'][0]['theorem_count'] == 17
names = []
for row in receipt['modules'] + receipt['dependency_rebuilds']:
    assert row['exit_code'] == 0 and row['status'] == 'PASS_FRESH_COMPILE_STANDARD_AXIOMS'
    assert sha(Path(row['log'])) == row['log_sha256']
    assert sha(Path(row['olean'])) == row['olean_sha256']
    assert sha(Path(row['instrumented_source'])) == row['instrumented_source_sha256']
    assert sha(Path(row['source_snapshot'])) == row['original_source_sha256']
    assert set(row['theorem_names']) == set(row['axioms'])
    for values in row['axioms'].values(): assert set(values) <= {'propext','Classical.choice','Quot.sound'}
    if row['new_module']: names += row['theorem_names']
assert len(set(names)) == len(names) == 28
num = receipt['numerical_replay']
assert num['status'] == 'PASS_EXACT_REPLAY' and num['falsifier_count'] == 13
assert num['analytical_payments_tested'] is False and num['global_D_N_estimated'] is False
assert all(row['all_fields_equal'] and row['all_bytes_equal'] for row in num['jsons'].values())
bindings = {p.relative_to(rnd).as_posix():sha(p) for p in sorted(rnd.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts and p.name != 'controller_manifest.json'}
manifest = dict(round=11, status='FINAL_AUXILIARY_IDENTITIES_WITH_OPEN_SIGNED_COMPENSATION',
 recorded_at_utc=datetime.now(timezone.utc).isoformat(), research_goal_active=True,
 objective_complete=False, victory=False, score=0,
 new_lean_modules=2, new_lean_conclusions=28,
 cumulative_auxiliary_modules=13, cumulative_auxiliary_conclusions=169,
 necessary_dependency_rebuilt=True, dependency_existing_conclusions_recounted=0,
 previous_artifacts_preserved=405, round10_artifacts_preserved=64,
 judge_production_snapshot_entries_verified=len(receipt['production_sha256_after']),
 source_hashes_match_judge=True, announced_final_hashes_match=True,
 no_test_reexecution_by_controller=True, no_old_custom_olean_reuse=True,
 source_adaptive_onset='u>=10^24', source54_literal_exponent='-sqrt(u/60)',
 weaker_majorant_used='-sqrt(u)/60',
 retained_ledger='D_N=B_prime^a9+B_pp^a9+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)',
 new_compiled_scope=['Actual squarefree finite lcm/totient coefficient B6 and unit wrapper over rational numbers',
 'Actual U2 physical J2 source bracket, two-kernel P1 local and entire finite partition with connected faces; actual singular-series P2 with entropy, singletons and geometric faces'],
 written_partial_payment=dict(term='Common model only, 3 coprime N',
 bound='(9/2) C_sieve S(N)^2 N/u^2+2S(N)sqrt(N), C_sieve=134217728/2541',
 budget='<1e-12N/(u logu) at u>=10^24 under source inputs', compiled=False,
 alternatives_not_added=['P4 central','P5 full common'], complete_pair_paid=False),
 unpaid=['H2+S(N)Delta_single+S(N)Delta_face plus J0/J1 relative to genuine favorable masses',
 'B13 guarded bilateral signed moment with preserved reference principal',
 'Additional effective physical-band BV onset','Covered term 2max(e,0)'],
 prefix_scope_warning='Whole U_a includes r<=alpha; paid annulus does not pay low prefix or remove source S(N)N.',
 technical_failed_attempts_preserved=3, preflight_failure_is_not_Lean=True,
 local_falsifiers=13, global_impossibility_inferred=False,
 judge_receipt_sha256=receipt_sha, judge_report_sha256=report_sha,
 bindings_sha256=bindings, original_sources_sha256=inputs['external_sha256'])
dest = rnd/'controller_manifest.json'
dest.write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=manifest['status'], files_bound=len(bindings),
 snapshot_entries_verified=manifest['judge_production_snapshot_entries_verified'],
 previous_preserved=405, new_theorems=28, cumulative=169, victory=False,
 controller_sha256=sha(dest)),ensure_ascii=False))
