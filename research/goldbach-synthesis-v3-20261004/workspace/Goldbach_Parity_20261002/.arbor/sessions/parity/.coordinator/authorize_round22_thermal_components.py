"""ROOT metadata gate only; no evaluator import, compilation or mathematical evaluation."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role6/thermal_h1'

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

prep_path = P / 'component_preparation22.json'
manifest_path = P / 'component_prepared_manifest22.json'
assert sha(prep_path) == 'b417be88862b3adb9636d90214243c943c4d8e054856dff3e93baf9be1280a5e'
assert sha(manifest_path) == 'e1d79e619115452582880ee6ab819582439127675a41e4d2c5ddbff14d4f1d8a'
prep, manifest = read(prep_path), read(manifest_path)
assert prep['status'] == 'PREPARED_SOURCE_ONLY_NOT_EXECUTED'
assert manifest['status'] == 'PREPARED_COMPONENT_SOURCES_ONLY_NOT_EXECUTED'
assert prep['actor'] == manifest['actor'] == 'ROLE6'
assert prep['bank_id'] == manifest['bank_id'] == 'THERMAL_COMPONENT_AUX22'
assert prep['scope'] == manifest['scope'] == 'THERMAL_COMPONENT_AUX_ONLY'
assert prep['binding_count'] == len(prep['bindings']) == 25
assert manifest['binding_count'] == len(manifest['bindings']) == 24
assert prep['bindings'][:-1] == manifest['bindings']
assert prep['captures_before_START'] == 27
assert prep['component_math_executions'] == prep['component_Lean_executions'] == 0
assert prep['old_producer_reexecutions'] == 0 and not prep['sole_attempt_consumed']
assert manifest['component_math_invocations'] == manifest['component_Lean_invocations'] == 0
assert manifest['old_bank_replays'] == manifest['runtime_probes'] == 0
assert not manifest['H1_claim'] and not manifest['WIN']
for row in prep['bindings']:
    path = Path(row['path'])
    assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)
assert sha(Path(prep['runtime_path'])) == '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
contract = read(P / 'component_contract22.json')
assert contract['full_result_case_count'] == prep['expected_case_count'] == 44
assert contract['gamma_phase_cases'] == prep['expected_Gamma_phase_cases'] == 15
assert contract['reference_cells_each'] == prep['expected_reference_cells_each'] == 2240
assert contract['reference_cells_total'] == prep['expected_reference_cells_total'] == 33600
assert contract['mutation_count'] == prep['expected_mutation_count'] == 19
assert contract['sqrt_certificates_expected'] == prep['expected_sqrt_certificates'] == 15
assert contract['old_results_as_inputs'] == []
for field in ('H1_numeric_claim', 'H1_formal_claim', 'coefficient_N_claim', 'D_N_claim', 'WIN'):
    assert contract[field] is False
archives = read(B / 'round22/previous_artifacts_sha256.json')
assert archives['file_count'] == len(archives['sha256']) == 3089
for relative, expected in archives['sha256'].items():
    assert sha(B / relative) == expected, relative
assert not (P / 'actual_component22').exists()
gate_path = C / 'messages/round22_thermal_component_authorization.json'
assert Path(prep['root_gate_path']) == gate_path
assert Path(prep['future_actual_directory']) == P / 'actual_component22'
gate = {
    'schema': 'ROUND22_THERMAL_COMPONENT_AUTHORIZATION_V1',
    'created_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'AUTHORIZED', 'actor': 'ROLE6',
    'bank_id': 'THERMAL_COMPONENT_AUX22', 'scope': 'THERMAL_COMPONENT_AUX_ONLY',
    'preparation_sha256': sha(prep_path), 'manifest_sha256': sha(manifest_path),
    'bindings': prep['bindings'], 'launcher_invocations_maximum': 1,
    'new_component_child_invocations_maximum': 1,
    'actual_directory': str(P / 'actual_component22'),
    'captures_before_START': 27, 'protected_archive_paths_verified': 3089,
    'root_FULL_reads': {
        'paper': '07e633', 'contract': 'cc7c6a', 'preparation': '9afcc0',
        'ground': 'e2f000', 'analytic': '648119', 'reference': 'fc0fd2',
        'kernel': 'b7c9c4', 'checker': 'fb5ff3', 'producer': 'abaa3a',
        'launcher': 'ec21d4', 'manifest': '55bf4a', 'scope': '8c15c4',
        'metadata_builder': '826b61', 'thermal_context_contract': '8c7d3e'},
    'mathematical_source_judgment_owner': 'ROLE6',
    'actor_prepared_source_receipt': 'fbdefa_exit0',
    'root_role': 'COORDINATOR_METADATA_ONLY_NO_MATHEMATICAL_REVIEW_CREDIT',
    'root_compiler_invocations': 0, 'root_numeric_invocations': 0,
    'old_bank_replays_allowed': 0, 'global_H1_invocations_allowed': 0,
    'Lean_invocations_allowed': 0, 'coefficient_N_invocations_allowed': 0,
    'no_credit_for_H1_Weil_heat_coefficientN_DN_WIN': True,
    'D_N_paid': False, 'WIN': False}
with gate_path.open('x', encoding='utf-8') as stream:
    json.dump(gate, stream, ensure_ascii=False, indent=2)
    stream.write('\n')
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
cp['phase'] = 'ROUND22_H1_COMPONENT_AUX_SINGLE_ATTEMPT_AUTHORIZED_PSI_C5_SOURCES_ACTIVE'
cp['previous_goal_turn_evidence'].append('.arbor/sessions/parity/.coordinator/messages/round22_thermal_component_authorization.json')
for actor in cp['in_flight_executors']:
    if actor['role'] == 6:
        actor['status'] = 'NEW_THERMAL_COMPONENT_AUX_SINGLE_ATTEMPT_AUTHORIZED_NOT_STARTED'
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps({'gate_path': str(gate_path), 'gate_sha256': sha(gate_path),
                  'bindings_verified': 25, 'protected_archive_paths_verified': 3089,
                  'root_math_executions': 0, 'root_Lean_executions': 0, 'WIN': False}, indent=2))
