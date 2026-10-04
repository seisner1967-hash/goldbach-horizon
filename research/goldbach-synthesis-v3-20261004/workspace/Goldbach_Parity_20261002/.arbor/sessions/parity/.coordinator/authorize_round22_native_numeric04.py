"""ROOT metadata-only authorization of the already reviewed fixed numeric consumer."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role3/native_numeric_consumer_source01'
H = B / 'round22/role4/circle_native_build_source04'
M = B / 'round22/role3/native_build_metadata04'
R = B / 'round22/role4/native_numeric04_consumer_review_source01'

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

def key(p):
    return str(p.resolve()).casefold()

def check(p, digest, size=None):
    assert p.is_file() and sha(p) == digest, str(p)
    assert size is None or p.stat().st_size == size, str(p)

parser = argparse.ArgumentParser()
for name in ('prep-sha', 'manifest-sha', 'metadata-receipt-path', 'metadata-receipt-sha',
             'builder-path', 'builder-sha', 'metadata-reads-path', 'metadata-reads-sha', 'ROOT-full-reads'):
    parser.add_argument('--' + name, required=True)
args = parser.parse_args()
prep_path, manifest_path = P / 'numeric_preparation22.json', P / 'numeric_manifest22.json'
meta_paths = [(prep_path, args.prep_sha), (manifest_path, args.manifest_sha),
              (Path(args.metadata_receipt_path), args.metadata_receipt_sha),
              (Path(args.builder_path), args.builder_sha),
              (Path(args.metadata_reads_path), args.metadata_reads_sha)]
for p, digest in meta_paths:
    assert p.resolve().is_relative_to(B.resolve())
    check(p, digest)

fixed = dict(scope='NATIVE_NUMERIC04_FULL_N1E8_ONLY', fixed_N=100000000,
    fixed_M=100000000, fixed_K=134217728, fixed_S='288230376151711744',
    max_children=2, max_retries=0, wall_seconds=3600, output_bytes=2147483648,
    commit_job_bytes=2147483648, rss_per_process_monitor_bytes=2147483648,
    sampled_job_rss_cap_bytes=4294967296, max_active_job_processes=16,
    max_total_job_processes=32, job_limit_flags_requested=8968,
    working_set_limit_flag_requested=False, rss_os_enforced=False,
    rss_control='SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM', log_bytes=1048576,
    metadata_bytes=16777216, capture_bytes=33554432, compiler_invocations=0)
locked = {
    P / 'run_native04_once22.py': '97473b226ce5206e021e444720651e00ca1fdb4c1c1052e20db60d4effec3f55',
    P / 'numeric_execution_plan22.json': 'c66808e4cd7312d76002559afccf909fdb5b6aa1e706301fc88813dcb519aaeb',
    P / 'numeric_trust_policy22.json': 'c6c97d0ef8846bbabb6db2ae7544de4aec631403c6f60ca460983c334059ebce',
    P / 'numeric_consumer_contract22.txt': '8be046b99950043cd684a1cee51d4b0d0ef933b791d357946ca0ce7689a2aac6',
    P / 'preparation_requirements22.txt': 'a6c36825ffb4e32838852852dbfe445ba9bcb9dab17bcf8482897d9d4e736c8c',
    P / 'source_handoff22.json': '0c839fc7c602c52c6c3f0d47d6f643342c8641a0cc8527b656a4e7cf70e74616',
    R / 'source_review22.json': 'f1afc6db690b7ee706f66d2ea9d14878eb36b3374eceffbadc6157e9c2cf9012',
    R / 'trust_review22.json': '5fdf1c49cef3b85d1b617d79b31cca39573c5bc964f23df1535f933406b5c2c7',
    H / 'windows_build_job22.py': '88d857ce33eece8f90906bc5088d5cac905b868e60ede1b6439b1a3af3126cc3',
    M / 'build_manifest22.json': '24ea81c9ae7134f71837baed91dabc9c64f45a2438ca6223e1aedc2154a85c2f',
    M / 'build_execution_closure22_revision02.json': 'dd506cebebcdbf7c75fd138d26cfb744552bdd6912e3cc37fbaa3a58fd8c0c15',
    H / 'actual_build04_attempt01/PRE.json': 'e751361aa2e9b20b7fae95b8c0fdda731338a0b7fb88c1f3aed4fb72d7ecc676',
}
for p, digest in locked.items():
    check(p, digest)
prep, manifest, plan = read(prep_path), read(manifest_path), read(P / 'numeric_execution_plan22.json')
assert prep['status'] == 'NATIVE_NUMERIC04_METADATA_PREPARED'
for name, value in fixed.items():
    assert type(prep[name]) is type(value) and prep[name] == value, name
    assert type(plan[name]) is type(value) and plan[name] == value, name
assert key(Path(prep['manifest_path'])) == key(manifest_path)
assert prep['manifest_sha256'] == args.manifest_sha
assert prep['source_handoff_sha256'] == locked[P / 'source_handoff22.json']
assert prep['numeric_execution_plan_sha256'] == locked[P / 'numeric_execution_plan22.json']
build_receipt_sha = '04ce22f9ee05215ee9c7c335b41755b1da4e001a82fa20085cfe7dccca1a7fc8'
build_plan_sha = '538cc14faf3466bb8a0505e8f6aae3007fc84b2b6246afb2da55d37be5718156'
assert prep['build_receipt_sha256'] == build_receipt_sha
assert prep['actual_build_plan_sha256'] == build_plan_sha
review, trust = read(R / 'source_review22.json'), read(R / 'trust_review22.json')
assert review['status'] == 'NUMERIC04_SOURCE_REVIEW_CLOSED_WITH_NATIVE_REFINEMENT_OPEN'
assert trust['status'] == 'NUMERIC04_FIXED_IMAGES_REVIEWED_WITH_EXPLICIT_WINDOWS_NATIVE_TRUST'
for doc in (review, trust):
    assert doc['reviewer'] == 'ROLE4' and doc['scope'] == fixed['scope']
    assert doc['unresolved_execution_blockers'] == []
    assert doc['parent_sha256'] == locked[P / 'run_native04_once22.py']
    assert doc['source_handoff_sha256'] == locked[P / 'source_handoff22.json']
    assert not doc['numeric_authorization'] and doc['produced_binary_invocations'] == 0
    for name in ('job_limit_flags_requested', 'working_set_limit_flag_requested', 'rss_os_enforced', 'rss_control'):
        assert doc[name] == fixed[name]
for name in ('effective_loads_observed', 'universal_loader_closure_verified', 'all_non_OS_imports_bound'):
    assert trust[name] is False
assert trust['installed_Windows_and_frozen_native_runtime_trusted'] is True

expected = {}
def add(path, digest, size=None, capture=False):
    p = Path(path)
    size = p.stat().st_size if size is None else size
    old = expected.get(key(p))
    assert old is None or (old['sha256'], old['bytes']) == (digest, size), str(p)
    expected[key(p)] = dict(path=str(p), sha256=digest, bytes=size,
                           capture=capture or (old is not None and old['capture']))

old = read(M / 'build_manifest22.json')['bindings']
assert len(old) == 6375
for row in old + read(P / 'source_handoff22.json')['bindings']:
    add(row['path'], row['sha256'], row['bytes'], row.get('capture', False))
closed = read(M / 'build_execution_closure22_revision02.json')
assert closed['parent_invocations'] == 1 and closed['parent_exit_code'] == 0
assert closed['compiler_processes_created'] == 2 and closed['produced_binary_invocations'] == 0
for row in closed['output_bindings'] + closed['binary_bindings']:
    add(row['path'], row['sha256'], row['bytes'])
captures = read(H / 'actual_build04_attempt01/PRE.json')['captures']
assert len(captures) == 47
for row in captures:
    add(row['original'], row['sha256'], capture=True)
    add(row['copy'], row['sha256'])
for p in (M / 'build_manifest22.json', M / 'build_execution_closure22_revision02.json',
          P / 'source_handoff22.json', R / 'source_review22.json', R / 'trust_review22.json'):
    add(p, locked[p], capture=True)
rows = manifest['bindings']
observed = {key(Path(row['path'])): row for row in rows}
assert len(rows) == len(observed) == len(expected) == prep['binding_count']
assert observed.keys() == expected.keys()
for path_key, row in expected.items():
    got = observed[path_key]
    assert (got['sha256'], got['bytes']) == (row['sha256'], row['bytes'])
    assert not row['capture'] or got.get('capture', False)
    check(Path(got['path']), got['sha256'], got['bytes'])
registry_path = B / 'round22/previous_artifacts_sha256.json'
check(registry_path, '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99')
registry = read(registry_path)['sha256']
assert len(registry) == 3089
for relative, digest in registry.items():
    p = (B / relative).resolve()
    assert p.is_relative_to(B.resolve())
    check(p, digest)
assert not (P / 'actual_numeric04_attempt01').exists()
cp = read(C / 'checkpoint.json')
assert cp['official_auxiliary_validation']['modules'] == 82
assert cp['official_auxiliary_validation']['declarations'] == 1367
gate = dict(fixed, schema='ROUND22_ROOT_NATIVE_NUMERIC04_AUTHORIZATION', status='AUTHORIZED',
    utc=datetime.now(timezone.utc).isoformat(), actor='ROLE6', attempt='actual_numeric04_attempt01',
    preparation_sha256=args.prep_sha, manifest_sha256=args.manifest_sha,
    source_handoff_sha256=locked[P / 'source_handoff22.json'],
    numeric_execution_plan_sha256=locked[P / 'numeric_execution_plan22.json'],
    numeric_trust_policy_sha256=locked[P / 'numeric_trust_policy22.json'],
    build_receipt_sha256=build_receipt_sha, actual_build_plan_sha256=build_plan_sha,
    binary_sha256=plan['binary_sha256'],
    independent_numeric_source_review_path=str(R / 'source_review22.json'),
    independent_numeric_source_review_sha256=locked[R / 'source_review22.json'],
    numeric_trust_review_path=str(R / 'trust_review22.json'),
    numeric_trust_review_sha256=locked[R / 'trust_review22.json'],
    accept_installed_Windows_and_frozen_native_runtime_trust=True,
    metadata_control_bindings=[dict(path=str(p), sha256=d) for p, d in meta_paths],
    ROOT_full_reads=args.ROOT_full_reads, inputs_verified=len(rows), archives_verified=3089,
    ROOT_compiler_invocations=0, ROOT_numeric_invocations=0,
    scope_note='Operational fixed-image test only; source reviews and Lean auxiliary proofs do not prove machine refinement or D_N.',
    effective_loads_observed=False, universal_loader_closure_verified=False,
    all_non_OS_imports_bound=False, native_Lean_refinement=False, D_N=False, WIN=False)
gate_path = C / 'messages/round22_native_numeric04_authorization.json'
with gate_path.open('x', encoding='utf-8') as f:
    json.dump(gate, f, ensure_ascii=False, indent=2)
    f.write('\n')
print(json.dumps(dict(gate=str(gate_path), gate_sha256=sha(gate_path), inputs=len(rows), archives=3089,
                     native_children_authorized_maximum=2, retries=0,
                     ROOT_compiler_invocations=0, ROOT_numeric_invocations=0, WIN=False)))
