"""ROOT metadata observation of BUILD04; executes neither compiler nor binaries."""
import argparse, hashlib, json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
H = B / 'round22/role4/circle_native_build_source04'
A = H / 'actual_build04_attempt01'
R = B / 'round22/role3/native_build_metadata04'
N = H.with_name('circle_native_revision02')

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''):
            h.update(block)
    return h.hexdigest()

def read(p):
    return json.loads(p.read_text(encoding='utf-8-sig'))

parser = argparse.ArgumentParser()
parser.add_argument('--closure-sha', required=True)
parser.add_argument('--ROOT-reads', required=True)
args = parser.parse_args()
assert sha(A / 'receipt.json') == '04ce22f9ee05215ee9c7c335b41755b1da4e001a82fa20085cfe7dccca1a7fc8'
assert sha(A / 'POST.json') == '165f1f9921570dc9075ab9abb6b300eb527891bb66aa4d9655efde32325cceab'
assert sha(N / 'build_receipt04.json') == sha(A / 'receipt.json')
closure_path = R / 'build_execution_closure22_revision02.json'
assert sha(closure_path) == args.closure_sha
r = read(A / 'receipt.json'); p = read(A / 'PRE.json')
post = read(A / 'POST.json'); d = read(closure_path)
assert r['status'] == 'NATIVE_BUILD_EXIT0' and r['error'] is None and r['post_error'] is None
assert post['all_inputs_controls_copies_archives_intact'] and post['post_error'] is None
assert len(r['results']) == 2 and r['child_exit_codes'] == [0, 0]
assert r['produced_binary_invocations'] == r['retry_count'] == 0
assert not r['numeric_authorization'] and not r['coefficient_N'] and not r['D_N'] and not r['WIN']
assert d['parent_invocations'] == 1 and d['parent_exit_code'] == 0
assert d['compiler_processes_created'] == 2 and d['produced_binary_invocations'] == 0
for row, tag in zip(r['results'], ['producer_build', 'checker_build']):
    assert row['tag'] == tag and row['pid'] > 0 and row['created_suspended'] and row['resumed']
    assert row['exit_code'] == 0 and row['wait_signalled'] and row['job_empty_confirmed']
    assert row['FIN_kind'] == 'CONFIRMED_DRIVER_AND_JOB_EXIT'
    assert row['termination_reason'] is None and row['api_or_control_error'] is None and not row['pipe_faults']
    assert row['commit_quota_bytes'] == 2147483648 and row['job_committed_memory_OS_limit_requested']
    assert row['job_limit_flags_requested'] == 8968 and not row['working_set_limit_flag_requested']
    assert not row['rss_os_enforced'] and row['rss_control'] == 'SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM'
    assert row['max_active_job_processes'] == 16 and row['max_total_job_processes'] == 32
    assert row['total_job_processes'] <= 32
    binary = N / 'build-final04' / (tag.replace('_build', '') + ('_dit22.exe' if tag == 'producer_build' else '_dif22.exe'))
    assert sha(binary) == row['binary_sha256']
for item in d['output_bindings']:
    path = Path(item['path'])
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
prep_path = H / 'build_preparation22.json'
assert sha(prep_path) == '4b2339ee900e2b3535ff038008936b209d6cfc10354a7f86d976516440b699ec'
prep = read(prep_path); manifest = Path(prep['manifest_path'])
assert sha(manifest) == prep['manifest_sha256'] == '24ea81c9ae7134f71837baed91dabc9c64f45a2438ca6223e1aedc2154a85c2f'
rows = read(manifest)['bindings']
assert len(rows) == prep['binding_count'] == 6375
for item in rows:
    path = Path(item['path'])
    assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256']
assert len(p['captures']) == 47
for item in p['captures']:
    assert sha(Path(item['original'])) == sha(Path(item['copy'])) == item['sha256']
assert sha(C / 'messages/round22_native_build04_authorization.json') == d['gate_sha256'] == '9000d3014dc0e5030aac6bcffdff54629af76861cc74630dee586265256ce643'
registry = B / 'round22/previous_artifacts_sha256.json'
assert sha(registry) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
archives = read(registry)['sha256']; assert len(archives) == 3089
for relative, digest in archives.items():
    path = (B / relative).resolve()
    assert path.is_relative_to(B.resolve()) and sha(path) == digest
cp_path = C / 'checkpoint.json'; cp = read(cp_path)
official = cp['official_auxiliary_validation']
assert official['modules'] == 80 and official['declarations'] == 1339
observation = dict(schema='ROUND22_ROOT_BUILD_ONLY04_CLOSED_OBSERVATION',
    time_utc=datetime.now(timezone.utc).isoformat(), status='NATIVE_BUILD_EXIT0',
    parent_invocations=1, compiler_driver_invocations=2, compiler_exit_codes=[0, 0],
    produced_binary_files=2, binary_sha256=r['binary_sha256'], produced_binary_invocations=0,
    retries=0, input_bindings_verified=6375, captures_originals_and_copies_verified=47, archives_verified=3089,
    ROLE6_closure_sha256=args.closure_sha, ROOT_reads=args.ROOT_reads,
    large_catalogue_scope='all entries parsed and bound bytes rehashed; no raw FULL source claim',
    official_modules=80, official_declarations=1339, auxiliary_Lean_count_change=0,
    rss_os_enforced=False, rss_control='SAMPLED_PROCESS_PEAK_AND_LIVE_JOB_SUM',
    job_limit_flags_requested=8968, ROOT_compiler_invocations=0, ROOT_numeric_invocations=0,
    effective_loads_observed=False, universal_loader_closure_verified=False,
    numeric_authorization=False, coefficient_N=False, D_N=False, WIN=False)
out = C / 'messages/round22_native_build04_closed_observation.json'
with out.open('x', encoding='utf-8') as f:
    json.dump(observation, f, ensure_ascii=False, indent=2); f.write('\n')
cp['phase'] = 'ROUND22_BUILD04_EXIT0_CONCRETE_ROOTS21_AND_NATIVE_CONSUMER_SOURCE_OPEN'
cp['last_progress'] = 'BUILD04 unique parent exit0, two compiler drivers exit0 and frozen images, no produced binary execution. Preserved6375inputs/47captures/3089archives. Official80/1339 unchanged; concrete Roots21 and numeric consumer source pending, coefficientN/D_N/WIN open.'
cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
cp['native_build04_closed_observation'] = observation
cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
with (B / 'REPORT.md').open('a', encoding='utf-8') as f:
    f.write('\n' + cp['last_progress'] + '\n')
print(json.dumps(observation, ensure_ascii=False, indent=2))
