"""Metadata-only ROOT observation of the closed Win32 control failure."""
import hashlib, json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
H = B / 'round22/role4/circle_native_build_source03'
A = H / 'actual_build03_attempt01'
R = B / 'round22/role3/native_build_metadata03'

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

assert sha(A / 'receipt.json') == '15e8e900446329515c1e30cd00ee03f73bd52715b28a3338dcfcb5741fd4f2c9'
assert sha(A / 'POST.json') == '75835f8730d0b4e9846e25b50f5f23c04e53d9cab74bf5156489ecc766b3e691'
assert sha(R / 'build_execution_closure22.json') == '94cdc97045004ddfca7556bac5a14339c247b7ead776373ec49d093edc25361e'
r = read(A / 'receipt.json')
p = read(A / 'PRE.json')
post = read(A / 'POST.json')
d = read(R / 'build_execution_closure22.json')
assert r['status'] == 'BUILD_STOP_NO_NUMERIC_VERDICT' and r['post_error'] is None
assert post['all_inputs_controls_copies_archives_intact']
assert len(r['results']) == 1
row = r['results'][0]
assert row['pid'] == 0 and not row['created_suspended'] and not row['resumed']
assert row['exit_code'] is None and row['total_job_processes'] == 0 and row['job_empty_confirmed']
assert row['api_or_control_error'] == 'OSError:[Errno 1314] SetInformationJobObject'
assert d['parent_invocations'] == 1 and d['parent_exit_code'] == 1
assert d['compiler_processes_created'] == d['produced_binary_invocations'] == 0
assert not (A / 'checker_build_START_REQUEST.json').exists()
assert not (A / 'producer_build_START.json').exists()
assert not list(H.with_name('circle_native_revision02').joinpath('build-final').iterdir())
assert not (H.with_name('circle_native_revision02') / 'build_receipt22.json').exists()
for item in d['output_bindings']:
    path = Path(item['path'])
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
prep_path = H / 'build_preparation22.json'
assert sha(prep_path) == '094a8459aba59ac402085988639ac7b7a4901d879e01646a27d67b0e57c3b4fc'
prep = read(prep_path)
manifest = Path(prep['manifest_path'])
assert sha(manifest) == prep['manifest_sha256'] == 'fdbdbb9f0fee7becc32f320b259ef0b2072dc18f257d8790c6ae9d4ba9607d50'
rows = read(manifest)['bindings']
assert len(rows) == prep['binding_count'] == 6358
for item in rows:
    path = Path(item['path'])
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
assert len(p['captures']) == 30
for item in p['captures']:
    assert sha(Path(item['original'])) == sha(Path(item['copy'])) == item['sha256']
assert sha(C / 'messages/round22_native_build03_authorization.json') == d['gate_sha256']
registry = B / 'round22/previous_artifacts_sha256.json'
assert sha(registry) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
archives = read(registry)['sha256']
assert len(archives) == 3089
for relative, digest in archives.items():
    path = (B / relative).resolve()
    assert path.is_relative_to(B.resolve()) and sha(path) == digest
cp_path = C / 'checkpoint.json'
cp = read(cp_path)
official = cp['official_auxiliary_validation']
assert official['modules'] == 78 and official['declarations'] == 1304
observation = dict(schema='ROUND22_ROOT_BUILD_ONLY03_CONTROL_FAILURE_OBSERVATION',
    time_utc=datetime.now(timezone.utc).isoformat(), status=d['status'],
    parent_invocations=1, compiler_processes_created=0, compiler_exit_code=None,
    failure=row['api_or_control_error'], failure_before_CreateProcess=True,
    checker_not_invoked=True, retries=0, produced_binary_files=0, produced_binary_invocations=0,
    input_bindings_verified=6358, captures_originals_and_copies_verified=30, archives_verified=3089,
    ROLE6_closure_sha256=sha(R / 'build_execution_closure22.json'),
    ROOT_reads='FIN-receipt-POST291b62;ROLE6closure-PREprojection26c896;prepba511f;contract-source-e08216;scope-fa0ab4',
    large_catalogue_scope='all entries parsed and bound bytes rehashed, no raw FULL source claim',
    official_modules=78, official_declarations=1304, technical_failure_not_math_refutation=True,
    auto_approval_rejection=False, ROOT_compiler_invocations=0, ROOT_numeric_invocations=0,
    effective_loads_observed=False, universal_loader_closure_verified=False,
    coefficient_N=False, D_N=False, WIN=False)
out = C / 'messages/round22_native_build03_closed_observation.json'
with out.open('x', encoding='utf-8') as f:
    json.dump(observation, f, ensure_ascii=False, indent=2)
    f.write('\n')
cp['phase'] = 'ROUND22_BUILD03_WIN32_CONTROL_FAIL_BEFORE_COMPILER_SOURCE04_AND_JUDGE19_PENDING'
cp['last_progress'] = 'BUILD03 unique parent exit1, Win32 SetInformationJobObject1314 before compiler creation; zero compiler/produced execution. Conserved6358inputs/30captures/3089archives. SOURCE04 resource repair and Gamma11 repair distinct, Judge19 FiniteField24 preparing; official78/1304, global D_N/WIN open.'
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
cp['native_build03_closed_observation'] = observation
for actor in cp['in_flight_executors']:
    actor['status'] = {3:'BUILD03_CLOSED_GAMMA_SOURCE_REPAIR_ACTIVE',4:'SOURCE_BUILD04_RESOURCE_REPAIR_ACTIVE',5:'FINITE_FIELD_BATCH19_METADATA_PREPARATION_ACTIVE'}.get(actor['role'], actor['status'])
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as f:
    f.write('\n' + cp['last_progress'] + '\n')
print(json.dumps(observation, ensure_ascii=False, indent=2))
