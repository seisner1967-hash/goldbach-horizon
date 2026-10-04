"""ROOT metadata gate for sourcepack02: hashes and shapes, no mathematical evaluation."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role3/performance_sourcepack02'
T = P / 'launch_prepare03'
PREP = T / 'preparation22.json'
MANIFEST = T / 'prepared_manifest22.json'
READS = T / 'metadata_execution_receipt22.json'
REVIEW = B / 'round22/judge5/performance_source_review02/review_receipt22.json'
GATE = C / 'messages/round22_global_thermal_h1_authorization02.json'
CLOSED = B / 'round22/role4/h1_global_numeric/launch_prepare02/actual_attempt01'
EVALUATION = 'PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER'
ANALYTIC = 'PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION'
EXPECTED = {
    PREP: '8d08bc4db8f702a53ae3340a2ba9102969caf7ea7995aa282638cd0e84919433',
    MANIFEST: '8ac1baa20b6418a8278ff74f4e9ae89c1b2a198d8e67ab841cb243192e35933d',
    READS: 'b560d5f6c5463d91688e9cda1053bc24dd508bc10d3450487a8adb2bd484b155',
    REVIEW: '638b1aaba849473a1806fe3b4bb967265b35f2ecb901b4003c0b661b114a1ddf',
    P / 'source_manifest22.json': '914c210931fb8029f59727a58b473402f8ec28c8e3e86328144e350d0fec362f',
    T / 'prepare_metadata_source22.ps1': 'f3cc88bcf976753ad768048ba6db41020edb9b2d0c77c8df3d00ed476d73d921',
    T / 'run_global_once_source22.py': 'e0486e0c004e53249d6b99ffa2aa908e01f456249b870d01dc8a54bcfa868c2d',
    T / 'thermal_child_source22.py': '402222f0538f3e9db72a0bb0f0bc4a2420b79ac9e1fe6d30822f80e83857819f',
    T / 'launch_contract_source22.md': 'd1df1f8907d5afffe9f1e56241d9d6e65088cc96529380d707ef3a4418c69409',
    T / 'resource_addendum_source22.md': '2d43730db7a5c28d2e35aae1600953cf6df8a191545d83160f63ec819631e2ef',
    T / 'tool_read_receipts22.json': 'a225725cf56af02f580b04ad098a55375230ad7c604fa4c60fed72a37e8a620b',
}

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))

def key(path):
    return str(Path(path).resolve()).casefold()

def verify(row, digest_field='sha256', path_field='path'):
    path = Path(row[path_field])
    assert sha(path) == row[digest_field] and path.stat().st_size == row['bytes'], str(path)

def signature(row):
    return key(row['path']), row['sha256'], row['bytes'], row.get('module_alias') or ''

for path, digest in EXPECTED.items():
    assert sha(path) == digest, str(path)
assert not GATE.exists() and not (T / 'actual_attempt01').exists()
prep, manifest, review, reads = map(read, (PREP, MANIFEST, REVIEW, READS))
assert prep['schema'] == 'ROUND22_GLOBAL_THERMAL_PREPARATION_22'
assert manifest['schema'] == 'ROUND22_GLOBAL_THERMAL_PREPARED_MANIFEST_22'
assert prep['status'] == manifest['status'] == reads['status'] == 'PREPARED_METADATA_ONLY_NOT_EXECUTED'
assert prep['actor'] == manifest['actor'] == reads['actor'] == 'ROLE6'
assert prep['metadata_owner'] == manifest['metadata_owner'] == 'ROLE3'
assert prep['scope'] == manifest['scope'] == 'ROUND22_GLOBAL_THERMAL_H1_NUMERIC_ONLY'
assert prep['bank_id'] == manifest['bank_id'] == 'THERMAL_GLOBAL_H1_22_SOURCEPACK02'
assert prep['source_manifest_sha256'] == manifest['source_manifest_sha256'] == EXPECTED[P / 'source_manifest22.json']
assert key(prep['root_gate_path']) == key(GATE)
assert key(prep['future_actual_directory']) == key(T / 'actual_attempt01')
assert key(prep['closed_attempt_directory']) == key(CLOSED)
assert key(prep['launcher_path']) == key(T / 'run_global_once_source22.py')
assert key(prep['child_path']) == key(T / 'thermal_child_source22.py')
assert prep['runtime_flags'] == reads['runtime_flags'] == ['-I', '-S', '-B', '-X', 'utf8']
assert sha(Path(prep['runtime_path'])) == reads['runtime_sha256'] == '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
limits = dict(max_children=1, retry_count=0, max_wall_seconds=10800, max_artifact_bytes=2147483648,
              expected_vertical_nodes=204800, expected_arch_nodes=12288, expected_arithmetic_integers=999999,
              catalogue_parameter_change_allowed=False)
assert prep['limits'] == limits
assert all(reads['limits'][name] == limits[name] for name in reads['limits'])
assert prep['structural_checker_alone_authorizes_PASS'] is False
assert prep['enclosure_review_required'] is prep['actual_boxtail_guard_required'] is True
bindings = prep['bindings']
assert len(bindings) == prep['binding_count'] == reads['bindings']['preparation_bindings'] == 1016
assert len({key(row['path']) for row in bindings}) == len(bindings)
assert len(manifest['bindings']) == manifest['binding_count'] == reads['bindings']['prepared_manifest_bindings'] == 1015
assert prep['prepared_manifest_sha256'] == reads['bindings']['prepared_manifest_sha256'] == EXPECTED[MANIFEST]
assert reads['bindings']['preparation_sha256'] == EXPECTED[PREP]
extra = [row for row in bindings if row['kind'] == 'PREPARED_MANIFEST']
assert len(extra) == 1 and key(extra[0]['path']) == key(MANIFEST)
assert [row for row in bindings if row['kind'] != 'PREPARED_MANIFEST'] == manifest['bindings']
for row in bindings:
    verify(row)
source = read(P / 'source_manifest22.json')
source_rows = source['core_bindings'] + source['support_bindings']
bound_source = [row for row in bindings if row.get('source_packet') is True]
assert len(source_rows) == len(bound_source) == prep['source_packet_bindings'] == manifest['source_packet_bindings'] == 21
assert {signature(row) for row in source_rows} == {signature(row) for row in bound_source}
assert {key(row['path']) for row in bound_source} == {key(path) for path in prep['source_packet_paths']}
aliases = [row for row in bindings if row.get('module_alias')]
assert sorted(row['module_alias'] for row in aliases) == sorted(prep['runtime_alias_order'])
assert prep['runtime_alias_order'] == source['runtime_alias_order'] == manifest['runtime_module_aliases']
assert len(aliases) == len(set(prep['runtime_alias_order'])) == 9
assert all(Path(row['path']).resolve().parent == P.resolve() for row in aliases)
assert sum(row['kind'].startswith('CANONICAL_PYTHON') for row in bindings) == prep['runtime_files'] == 972
assert review['schema'] == 'ROUND22_PERFORMANCE_SOURCEPACK02_INDEPENDENT_REVIEW22'
assert review['status'] == 'SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED'
assert review['reviewer'] == reads['independent_reviewer'] == 'ROLE5'
assert review['source_author'] == reads['source_author'] == 'ROLE3'
assert review['reviewer_distinct_from_SOURCE_AUTHOR'] is True and review['unresolved_blockers'] == []
flags = ('primitive_enclosures_source_audited', 'analytic_remainders_source_audited',
         'integer_endpoint_equivalence_source_audited', 'Gamma_value_projection_source_audited',
         'fresh_constant_cache_source_audited', 'launch_tools_source_audited',
         'resource_addendum_source_audited', 'same_math_parameters')
assert all(review[name] is True for name in flags)
assert review['global_h1_formal_proof'] is False
assert review['structural_checker_is_interval_certificate'] is review['structural_PASS_is_enclosure_PASS'] is False
assert prep['future_evaluation_level'] == manifest['future_evaluation_level'] == review['future_evaluation_level'] == EVALUATION
assert prep['analytic_certification_level'] == manifest['analytic_certification_level'] == review['analytic_certification_level'] == ANALYTIC
assert prep['structural_PASS_is_enclosure_PASS'] is manifest['structural_PASS_is_enclosure_PASS'] is False
for field, path, expected in (
    ('independent_review_receipt_sha256', REVIEW, EXPECTED[REVIEW]),
    ('independent_review_report_sha256', Path(review['review_report_path']), 'dfdc7d3a573c9d31364e198b8db749216316bec2162b19f4533babc1d2005286'),
    ('independent_domain_addendum_sha256', Path(review['domain_addendum_path']), '821d67b2f8448533d707e9e23a5c33c44c4b316b297bb7f8129ac8f7d89cb4b7'),
    ('resource_addendum_sha256', T / 'resource_addendum_source22.md', EXPECTED[T / 'resource_addendum_source22.md']),
):
    assert sha(path) == prep[field] == manifest[field] == expected
    assert any(key(row['path']) == key(path) and row['sha256'] == expected for row in bindings)
assert review['source_manifest_sha256'] == prep['source_manifest_sha256']
assert review['resource_addendum_sha256'] == prep['resource_addendum_sha256']
assert len(review['tool_bindings']) == 5
assert {key(row['path']) for row in review['tool_bindings']} == {key(T / name) for name in (
    'prepare_metadata_source22.ps1', 'run_global_once_source22.py', 'thermal_child_source22.py',
    'launch_contract_source22.md', 'resource_addendum_source22.md')}
for row in review['tool_bindings']:
    verify(row)
    assert any(signature(item)[:3] == signature(row)[:3] for item in bindings)
assert reads['schema'] == 'ROUND22_LAUNCH03_ACTUAL_METADATA_AND_PRELAUNCH_READS22'
assert reads['actual_builder_invocation']['invocations'] == 1 and reads['actual_builder_invocation']['exit_code'] == 0
assert reads['actual_builder_invocation']['metadata_only'] is True
assert reads['actual_builder_invocation']['builder_source_sha256'] == EXPECTED[T / 'prepare_metadata_source22.ps1']
assert reads['controller_authorized'] is False and reads['mathematical_children_started'] == 0
assert reads['Python_imports'] == reads['Python_parsers'] == 0 and reads['WIN'] is False
assert reads['bindings']['closed_attempt_integrity_verified'] is manifest['closed_attempt_integrity_verified'] is True
known = {
    'receipt.json': '2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93',
    'FIN.json': '2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93',
    'PREEXEC.json': 'b3734e005f391ddeef49c2342a8775218640c2c0e42e9146077008bb47dda4e3',
    'POSTEXEC.json': '3465bc934e6cab3dd204c3d0f3a939704a392b0beac32f123b081f3c6199eacf',
    'START.json': '7ccb60ee859d294902753afbb0cc939d5f5911d0c1ed7f81a3cef2c488d15683',
    'child_START.json': '119fa6abf5b4783c5fa0f8dec7322eb6aafdc125e2beeebf5eb181902413d730',
    'child_context.json': '902ab13f6ca89da54ca6a5fe41a28896e32d32ea8894c9cfe687ee9d7521cf9b',
    'attempt_reservation.json': 'aa506752807f540c48deead34c52a03e938d45315f8d7f39c1f1d692600325a7',
}
for name, digest in known.items():
    assert sha(CLOSED / name) == digest
closed_receipt, closed_pre = read(CLOSED / 'receipt.json'), read(CLOSED / 'PREEXEC.json')
assert closed_receipt['resource_failure'] == 'MAX_WALL_SECONDS' and closed_receipt['mathematical_children_started'] == 1
assert closed_receipt['retries'] == 0 and closed_receipt['post_integrity'] is True
assert len(closed_pre['bindings']) == 1003 and len(closed_pre['captures']) == 1005
for row in closed_pre['bindings']:
    verify(row, 'expected_sha256')
for row in closed_pre['captures']:
    verify(row, path_field='copy')
    verify(row, path_field='original')
assert len(closed_receipt['outputs']) == 3
for row in closed_receipt['outputs']:
    assert Path(row['path']).resolve().is_relative_to(CLOSED.resolve())
    verify(row)
registry_path = B / 'round22/previous_artifacts_sha256.json'
assert sha(registry_path) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
registry = read(registry_path)
assert len(registry['sha256']) == registry['file_count'] == 3089
for relative, digest in registry['sha256'].items():
    path = (B / relative).resolve()
    assert path.is_relative_to(B.resolve()) and sha(path) == digest
gate = dict(schema='ROUND22_ROOT_GLOBAL_THERMAL_AUTHORIZATION_22', status='AUTHORIZED',
    created_utc=datetime.now(timezone.utc).isoformat(), actor='ROLE6', metadata_owner='ROLE3',
    scope=prep['scope'], bank_id=prep['bank_id'], preparation_sha256=EXPECTED[PREP],
    bindings=bindings, limits=limits,
    independent_review_receipt_sha256=EXPECTED[REVIEW],
    independent_review_report_sha256=prep['independent_review_report_sha256'],
    independent_domain_addendum_sha256=prep['independent_domain_addendum_sha256'],
    resource_addendum_sha256=prep['resource_addendum_sha256'],
    future_evaluation_level=EVALUATION, analytic_certification_level=ANALYTIC,
    structural_PASS_is_enclosure_PASS=False, role6_prelaunch_read_receipt_sha256=EXPECTED[READS],
    ROOT_read_scopes=dict(tools_FULL=['3437eb','e59655','4cb754','4cc09c'],
        independent_report_FULL='73eb82', independent_domain_FULL='57c8ad', independent_receipt_FULL='ea7da0',
        role6_metadata_and_prelaunch_FULL='d927a4', preparation_manifest_headers_projection='4ec4f8',
        source_manifest_projection='8d9916', full_raw_runtime_inventory_read=False,
        all_bound_bytes_hash_verified=True),
    closed_original_inputs_verified=1003, closed_captures_verified=1005, closed_outputs_verified=3,
    protected_archives_verified=3089, previous_numeric_values_reused=False,
    ROOT_action='metadata authorization only; no numerical evaluation or Lean compilation',
    new_math_children_started=0, new_Lean_invocations=0, old_bank_replays=0,
    formal_H1='OPEN', horizontal_volet='UNIMPLEMENTED', coefficient_N='OPEN', D_N='UNPAID', WIN=False)
with GATE.open('x', encoding='utf-8', newline='\n') as stream:
    json.dump(gate, stream, indent=2, sort_keys=True)
    stream.write('\n')
print(json.dumps(dict(gate_path=str(GATE), gate_sha256=sha(GATE),
    bound_files_verified=len(bindings), protected_archives_verified=3089,
    closed_inputs_verified=1003, closed_captures_verified=1005, closed_outputs_verified=3,
    role6_numeric_invocation_authorized=1, ROOT_numeric_invocations=0, WIN=False)))
