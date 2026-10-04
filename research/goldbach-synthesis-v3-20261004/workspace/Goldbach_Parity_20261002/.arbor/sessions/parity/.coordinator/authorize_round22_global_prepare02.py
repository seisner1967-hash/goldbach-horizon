"""ROOT metadata gate only: hash/shape checks; no mathematical evaluator/import."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

BASE = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
COORD = BASE / '.arbor/sessions/parity/.coordinator'
PACK = BASE / 'round22/role4/h1_global_numeric'
TOOLS = PACK / 'launch_prepare02'
PREP = TOOLS / 'preparation22.json'
MANIFEST = TOOLS / 'prepared_manifest22.json'
GATE = COORD / 'messages/round22_global_thermal_h1_authorization01.json'
ROLE6_READ = BASE / 'round22/role3/global_h1_execution02/prelaunch_read_receipt22.json'
EXPECTED = {
    PREP: '60f88dc205fd8f9c6a4953bf9bc5b5d0d38522329fde9399c9b75118e6b12cba',
    MANIFEST: 'afe78750ae9d7c9d89199c82561c09ef7b72804bd56963c3eed959681e4b2b24',
    PACK / 'source_manifest22.json': 'e1caa3d115dd492cfa6d91478240b0e8418614b6faf8798f48e15312dfe11a51',
    TOOLS / 'prepare_metadata_source22.ps1': '6d6136ecae7736e81eaae725aab1f52094b84652454280b5c417ae0462bd83ff',
    TOOLS / 'run_global_once_source22.py': '0b2d45142e9bdeda91fa9d4d5d3f2e636439eed24a3503a973ac4e8f6e0299ae',
    TOOLS / 'thermal_child_source22.py': '059860cb5578dda6a6e0a700bd4c7896cc1469752581c44ef3882620dc7e27c6',
    TOOLS / 'launch_contract_source22.md': 'ad782625a35f32a3c2e48451cdf43521df2a25b5c2b7b8fb92d9e9133654d8b3',
    ROLE6_READ: '87c66a6f9db91a05cb1ccc7da783d4bbfb3b00db5c9c7b34fc9042e76db40d67',
    TOOLS / 'preparation_closure22.md': 'dd74933b21d4a2ea7b75526a0299e8724ae8ee864fe6c2f862387e194837bc56',
    TOOLS / 'read_receipts22.json': '87dda4b71073cf9a9f509981d44052c9ee10011d87ab2c34faa5845b488347bc',
}


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            digest.update(block)
    return digest.hexdigest()


def read(path):
    return json.loads(path.read_text(encoding='utf-8'))


def key(path):
    return str(Path(path).resolve()).casefold()


for path, expected in EXPECTED.items():
    assert sha(path) == expected, str(path)
assert not GATE.exists()
assert not (TOOLS / 'actual_attempt01').exists()
assert not (PACK / 'launch_prepare01/actual_attempt01').exists()
prep, manifest = read(PREP), read(MANIFEST)
assert prep['schema'] == 'ROUND22_GLOBAL_THERMAL_PREPARATION_22'
assert manifest['schema'] == 'ROUND22_GLOBAL_THERMAL_PREPARED_MANIFEST_22'
assert prep['status'] == manifest['status'] == 'PREPARED_METADATA_ONLY_NOT_EXECUTED'
assert prep['actor'] == manifest['actor'] == 'ROLE6'
assert prep['metadata_owner'] == manifest['metadata_owner'] == 'ROLE4'
assert prep['scope'] == 'ROUND22_GLOBAL_THERMAL_H1_NUMERIC_ONLY'
assert prep['bank_id'] == 'THERMAL_GLOBAL_H1_22_SOURCEPACK01'
assert key(prep['root_gate_path']) == key(GATE)
assert prep['runtime_flags'] == ['-I', '-S', '-B', '-X', 'utf8']
assert prep['limits'] == {
    'max_wall_seconds': 3600, 'max_artifact_bytes': 2147483648,
    'max_children': 1, 'retry_count': 0, 'expected_vertical_nodes': 204800,
    'expected_arch_nodes': 12288, 'expected_arithmetic_integers': 999999,
    'catalogue_parameter_change_allowed': False,
}
bindings = prep['bindings']
assert len(bindings) == prep['binding_count'] == 1003
assert len({key(x['path']) for x in bindings}) == 1003
assert len(manifest['bindings']) == manifest['binding_count'] == 1002
extra = [x for x in bindings if x['kind'] == 'PREPARED_MANIFEST']
assert len(extra) == 1 and key(extra[0]['path']) == key(MANIFEST)
assert [x for x in bindings if x['kind'] != 'PREPARED_MANIFEST'] == manifest['bindings']
for binding in bindings:
    path = Path(binding['path'])
    assert sha(path) == binding['sha256'] and path.stat().st_size == binding['bytes'], str(path)
source = read(PACK / 'source_manifest22.json')
source_bindings = [x for x in bindings if x['kind'] == 'SOURCE_PACKET_INPUT']
assert len(source_bindings) == len(source['bindings']) == 14
normalize = lambda x: (key(x['path']), x['sha256'], x['bytes'], x.get('module_alias') or '')
assert {normalize(x) for x in source_bindings} == {normalize(x) for x in source['bindings']}
assert sorted(x['module_alias'] for x in source_bindings if x['module_alias']) == sorted(prep['runtime_alias_order'])
assert len(prep['runtime_alias_order']) == len(set(prep['runtime_alias_order'])) == 9
assert sum(x['kind'].startswith('CANONICAL_PYTHON') for x in bindings) == 972
assert sum(x['kind'] == 'PREVIOUS_METADATA_FAILURE_BYTES_READONLY' for x in bindings) == 6
review_binding = [x for x in bindings if x['kind'] == 'INDEPENDENT_SOURCE_REVIEW_RECEIPT']
assert len(review_binding) == 1
review = read(Path(review_binding[0]['path']))
assert review_binding[0]['sha256'] == '973da581891aa1c1746999efd7684a88507feaae0e2b83b80197bb01a61217b6'
assert review['status'] == 'SOURCE_REVIEW_NUMERICAL_ENCLOSURES_CLOSED'
assert review['unresolved_blockers'] == [] and review['reviewer_distinct_from_ROLE4'] is True
assert review['primitive_enclosures_source_audited'] is True
assert review['analytic_remainders_source_audited'] is True
assert review['global_h1_formal_proof'] is False
assert prep['future_evaluation_level'] == review['future_evaluation_level'] == 'PAPER_AUDITED_DIRECTED_INTERVAL_PRODUCER_WITH_INDEPENDENT_STRUCTURAL_CHECKER'
assert prep['analytic_certification_level'] == review['analytic_certification_level'] == 'PAPER_DERIVATIONS_WITH_EXACT_DOMAINS_NOT_LEAN_CERTIFICATION'
assert prep['structural_PASS_is_enclosure_PASS'] is review['structural_PASS_is_enclosure_PASS'] is False
assert read(ROLE6_READ)['tools_source_unresolved_blockers'] == []
registry_path = BASE / 'round22/previous_artifacts_sha256.json'
assert sha(registry_path) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
registry = read(registry_path)
assert registry['file_count'] == len(registry['sha256']) == 3089
for relative, expected in registry['sha256'].items():
    path = (BASE / relative).resolve()
    assert path.is_relative_to(BASE.resolve()) and sha(path) == expected, relative
gate = dict(
    schema='ROUND22_ROOT_GLOBAL_THERMAL_AUTHORIZATION_22', status='AUTHORIZED',
    created_utc=datetime.now(timezone.utc).isoformat(), actor=prep['actor'],
    metadata_owner=prep['metadata_owner'], scope=prep['scope'], bank_id=prep['bank_id'],
    preparation_sha256=EXPECTED[PREP], bindings=bindings, limits=prep['limits'],
    independent_review_receipt_sha256=prep['independent_review_receipt_sha256'],
    independent_review_report_sha256=prep['independent_review_report_sha256'],
    independent_domain_addendum_sha256=prep['independent_domain_addendum_sha256'],
    future_evaluation_level=prep['future_evaluation_level'],
    analytic_certification_level=prep['analytic_certification_level'],
    structural_PASS_is_enclosure_PASS=False, role6_prelaunch_read_receipt_sha256=EXPECTED[ROLE6_READ],
    ROOT_read_scopes=dict(tools_FULL=['b27aed','f3ff42','52dc7c','107bc8','cb171d'],
        preparation_nonruntime_projection='5af93e', ROLE6_receipt_FULL='184808',
        tools_receipt_FULL='7e454e', closure_FULL='3123ca',
        full_runtime_inventory_text_read=False, all_bound_bytes_hash_verified=True),
    ROOT_action='metadata authorization only; ROOT performs no numerical evaluation or Lean compilation',
    new_math_children_started=0, new_Lean_invocations=0, old_bank_replays=0,
    formal_H1='OPEN', horizontal_volet='UNIMPLEMENTED', coefficient_N='OPEN', D_N='UNPAID', WIN=False,
)
with GATE.open('x', encoding='utf-8', newline='\n') as target:
    json.dump(gate, target, indent=2, sort_keys=True)
    target.write('\n')
print(json.dumps(dict(gate_path=str(GATE), gate_sha256=sha(GATE),
    bound_files_verified=1003, protected_archives_verified=3089,
    role6_numeric_invocation_authorized=1, ROOT_numeric_invocations=0, WIN=False)))
