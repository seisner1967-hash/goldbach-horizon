"""ROOT metadata only: authorize two fixed builds, never execute a compiler."""
import argparse, hashlib, json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
H = B / 'round22/role4/circle_native_build_source03'
N = H.with_name('circle_native_revision02')

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

parser = argparse.ArgumentParser()
parser.add_argument('--preparation-sha', required=True)
parser.add_argument('--manifest-sha', required=True)
parser.add_argument('--ROOT-read-receipts', required=True)
args = parser.parse_args()
prep_path = H / 'build_preparation22.json'
assert sha(prep_path) == args.preparation_sha
prep = read(prep_path)
assert prep['status'] == 'BUILD_ONLY_METADATA_PREPARED'
fixed = {'scope': 'NATIVE_BUILD_ONLY_TWO_FIXED_TARGETS', 'max_driver_invocations': 2,
    'max_retries': 0, 'wall_seconds': 300, 'max_active_job_processes': 16,
    'max_total_job_processes': 32, 'commit_job_bytes': 2147483648,
    'rss_per_process_bytes': 2147483648, 'sampled_job_rss_bytes': 4294967296,
    'log_bytes': 1048576, 'capture_bytes': 33554432, 'metadata_bytes': 16777216,
    'binary_bytes_each': 67108864, 'temporary_bytes': 67108864,
    'output_bytes': 268435456, 'produced_binary_invocations': 0}
assert all(prep.get(k) == v for k, v in fixed.items())
assert prep['accept_installed_Windows_and_GCC_trust'] is True
assert prep['compiler_trust_policy_sha256'] == '72fd49d993e3291a174d4ba5a139a649ab916e9e757274c0e89f0a6092b4f6a6'
assert prep['actual_build_plan_sha256'] == 'fc77f58cc215b1851e5a87b164407aadcc5cd8f2c7621dcccc6e0c3c38f13f61'
manifest_path = Path(prep['manifest_path'])
assert manifest_path.resolve().is_relative_to(B.resolve())
assert sha(manifest_path) == prep['manifest_sha256'] == args.manifest_sha
rows = read(manifest_path)['bindings']
by_path = {key(Path(row['path'])): row for row in rows}
assert len(rows) == len(by_path) == prep['binding_count']
controls = [(N / 'closure_snapshot22.json', '12bd8ab8c067e4881b837689ce705e7f029826b20482b85fbc6a6d18e3717e06'),
    (N / 'source_handoff22.json', '889d4e221911bdfe75104361d62f36accf3770a17f48f29d84a9ba8d1952da88'),
    (H / 'source_handoff22.json', '426074681af64190ea25ed1cb03229af34f8d26f490ebdc9b23e3dc240a8f07a')]
expected = {}
for path, digest in controls:
    assert sha(path) == digest
    for row in read(path)['bindings']:
        row_key = key(Path(row['path']))
        if row_key in expected:
            assert (expected[row_key]['sha256'], expected[row_key]['bytes']) == (row['sha256'], row['bytes'])
        expected[row_key] = row
review = B / 'round22/judge5/circle_native_build_controls_source_review03.md'
trust = B / 'round22/judge5/circle_native_build_trust_review03.json'
assert sha(review) == '514419b15d0e17300e852f4baec4bb3046f4f65c5f1da470f8faab125637cad2'
assert sha(trust) == '3d47ef4040924caec5c863b7009b389830bc4f1a2e97a46cd675e4a679fd14bd'
assert set(by_path) == set(expected) | {key(review), key(trust)} | {key(p) for p, _ in controls}
for row_key, frozen in expected.items():
    actual = by_path[row_key]
    assert (actual['sha256'], actual['bytes']) == (frozen['sha256'], frozen['bytes'])
    assert not frozen.get('capture', False) or actual.get('capture', False)
for row in rows:
    p = Path(row['path'])
    assert p.stat().st_size == row['bytes'] and sha(p) == row['sha256'], str(p)
td = read(trust)
assert td['status'] == 'BUILD_ONLY_DECLARED_IMPORTS_REVIEWED_WITH_EXPLICIT_WINDOWS_GCC_TRUST'
assert td['installed_Windows_and_GCC_trusted'] is True
assert td['effective_loads_observed'] is False and td['universal_loader_closure_verified'] is False
assert td['all_non_OS_imports_bound'] is False and td['numeric_authorization'] is False
registry = B / 'round22/previous_artifacts_sha256.json'
assert sha(registry) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
archive = read(registry)
assert archive['file_count'] == len(archive['sha256']) == 3089
for relative, digest in archive['sha256'].items():
    p = (B / relative).resolve()
    assert p.is_relative_to(B.resolve()) and sha(p) == digest
assert not (H / 'actual_build03_attempt01').exists()
assert not (N / 'build-final').exists() and not (N / 'build_receipt22.json').exists()
gate = dict(fixed, status='AUTHORIZED', time_utc=datetime.now(timezone.utc).isoformat(),
    schema='ROUND22_ROOT_BUILD_ONLY03_AUTHORIZATION', preparation_sha256=args.preparation_sha,
    manifest_sha256=args.manifest_sha, compiler_trust_policy_sha256=prep['compiler_trust_policy_sha256'],
    actual_build_plan_sha256=prep['actual_build_plan_sha256'], accept_installed_Windows_and_GCC_trust=True,
    independent_build_source_review_path=str(review), independent_build_source_review_sha256=sha(review),
    compiler_build_trust_review_path=str(trust), compiler_build_trust_review_sha256=sha(trust),
    ROOT_read_receipts=args.ROOT_read_receipts, all_binding_bytes_verified=len(rows),
    archives_verified=3089, effective_loads_observed=False, universal_loader_closure_verified=False,
    numeric_authorization=False, ROOT_compiler_invocations=0, ROOT_numeric_invocations=0,
    parent_flags_required=['-I', '-S', '-B', '-X', 'utf8'], D_N=False, WIN=False)
out = C / 'messages/round22_native_build03_authorization.json'
with out.open('x', encoding='utf-8') as f:
    json.dump(gate, f, ensure_ascii=False, indent=2)
    f.write('\n')
print(json.dumps(dict(gate=str(out), gate_sha256=sha(out), bindings=len(rows), archives=3089,
    compiler_invocations=0, produced_binary_invocations=0, D_N=False, WIN=False)))
