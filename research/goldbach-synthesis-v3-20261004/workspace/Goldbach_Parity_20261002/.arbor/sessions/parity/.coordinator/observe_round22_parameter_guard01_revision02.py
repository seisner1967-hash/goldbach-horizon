"""ROOT metadata observation only: no numeric recomputation or candidate import."""
import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
P = B / 'round22/role4/parameter_guard01_revision02'
A = P / 'actual_attempt01'

def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1048576), b''):
            value.update(block)
    return value.hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def main():
    parser = argparse.ArgumentParser()
    for name in ['receipt-sha', 'closure-path', 'closure-sha', 'ROOT-full-read-receipts']:
        parser.add_argument('--' + name, required=True)
    args = parser.parse_args()
    assert sha(A / 'receipt.json') == args.receipt_sha
    closure = Path(args.closure_path).resolve()
    assert closure.is_relative_to((B / 'round22/role3/parameter_guard01_revision02_execution').resolve())
    assert sha(closure) == args.closure_sha
    r = read(A / 'receipt.json')
    pre = read(A / 'PREEXEC.json')
    post = read(A / 'POSTEXEC.json')
    fin = read(A / 'FIN.json')
    start = read(A / 'START.json')
    spawn = read(A / 'SPAWN.json')
    status = 'PARAMETER_GUARDS_AND_FIVE_LOG_SAMPLES_AUX_PASS'
    assert r['status'] == fin['status'] == status
    assert r['scope'] == 'PARAMETER_GUARD01_ONLY'
    assert r['exit_code'] == fin['exit_code'] == 0
    assert r['children_started'] == fin['children_started'] == 1
    assert r['conservation_error'] is None and r['parse_error'] is None
    assert fin['stop'] is None and fin['spawn_error'] is None
    assert pre['token'] == start['token'] == spawn['token'] == fin['token']
    assert r['actual_pid'] == fin['actual_pid'] == spawn['actual_pid']
    assert pre['children_started'] == 0 and start['max_children'] == 1 and start['max_retries'] == 0
    assert pre['input_count'] == post['input_count'] == 1005
    assert pre['all_inputs_intact'] and post['all_inputs_intact']
    assert post['conservation_error'] is None and post['parse_error'] is None
    assert pre['archives']['unchanged'] and post['archives']['unchanged']
    for flag in ['global_projection', 'formal_primitives', 'D_N', 'WIN']:
        assert r[flag] is False
    assert sha(P / 'preparation22.json') == r['preparation_sha256'] == 'f10fc82a11d5120bbdb218d1c23eb8b5d96f95ae330506155246452078e6e506'
    prep = read(P / 'preparation22.json')
    manifest = Path(prep['manifest_path'])
    assert sha(manifest) == prep['manifest_sha256'] == 'a849df7b32dfe05a495a32bd989a200fac4d93b2703e57231bda381a4a6ba33a'
    bindings = read(manifest)['bindings']
    assert len(bindings) == len({str(Path(x['path']).resolve()).casefold() for x in bindings}) == 1005
    for item in bindings:
        path = Path(item['path'])
        assert path.stat().st_size == item['bytes'] and sha(path) == item['sha256'], str(path)
    gate_path = C / 'messages/round22_parameter_guard01_authorization.json'
    assert sha(gate_path) == r['gate_sha256'] == pre['gate_sha256'] == 'f2f00ac117694c747fca86e523741a85870e994627a40f8a6791653ba27d3cc8'
    gate = read(gate_path)
    assert gate['source_revision'] == 'revision02' and gate['scope'] == r['scope']
    review = Path(gate['independent_source_review_path'])
    assert sha(review) == gate['independent_source_review_sha256'] == '50240b80c6daad2af675ebaf87bef546c59190bc2b57e94e048576818cb1d269'
    for item in pre['captured']:
        assert sha(Path(item['original'])) == sha(Path(item['copy'])) == item['sha256']
        assert Path(item['copy']).stat().st_size == item['bytes']
    command = start['command']
    assert Path(command[0]).resolve() == Path(prep['canonical_python']).resolve()
    assert command[1:6] == ['-I', '-S', '-B', '-X', 'utf8']
    selected = {str(Path(x['copy']).resolve()): Path(x['original']).name for x in pre['captured']}
    assert selected[str(Path(command[6]).resolve())] == 'parameter_guard22.py'
    assert selected[str(Path(command[7]).resolve())] == 'fixed_parameter_log_model22.py'
    assert sha(A / 'stdout.log') == r['stdout_sha256']
    assert sha(A / 'stderr.log') == r['stderr_sha256']
    result = read(A / 'stdout.log')
    assert result['schema'] == 'ROUND22_PARAMETER_GUARD01_RESULT'
    assert result['scope'] == r['scope'] and result['status'] == status
    assert len(result['samples']) == 5 and len(result['mutations']) == 4
    assert [x['argument'] for x in result['samples']] == prep['samples']
    assert all(x['rejected'] for x in result['mutations'])
    assert all(not x['argument_primality_claimed'] for x in result['samples'])
    for flag in ['global_NTT_computed', 'complete_catalogue_checked', 'coefficient_N_computed', 'log_primitive_Lean_certified', 'spectral_H1', 'D_N', 'WIN']:
        assert result[flag] is False
    assert sum(p.stat().st_size for p in A.rglob('*') if p.is_file()) <= prep['output_bytes']
    registry_path = B / 'round22/previous_artifacts_sha256.json'
    assert sha(registry_path) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
    registry = read(registry_path)
    assert registry['file_count'] == len(registry['sha256']) == 3089
    for name, digest in registry['sha256'].items():
        path = (B / name).resolve()
        assert path.is_relative_to(B.resolve()) and sha(path) == digest, name
    assert not (B / 'round22/role4/parameter_guard01/actual_attempt01').exists()
    cp_path = C / 'checkpoint.json'
    cp = read(cp_path)
    observation = dict(schema='ROUND22_ROOT_PARAMETER_GUARD01_REVISION02_CLOSED_OBSERVATION',
        time_utc=datetime.now(timezone.utc).isoformat(), status=status, scope=r['scope'],
        receipt_sha256=args.receipt_sha, closure_path=str(closure), closure_sha256=args.closure_sha,
        ROOT_FULL_read_receipts=args.ROOT_full_read_receipts,
        actual_child_invocations=1, retries=0, inputs_verified=1005,
        protected_archives_verified=3089, captures_verified=len(pre['captured']),
        original_manifest_review_and_each_capture_preserved=True,
        sample_count=5, mutation_count=4, numeric_recomputation_by_ROOT=False,
        primitives_level='PAPER_AUDITED_NOT_LEAN_CERTIFIED',
        official_credit_added=0, official_modules=cp['official_auxiliary_validation']['modules'],
        official_declarations=cp['official_auxiliary_validation']['declarations'],
        ROOT_numeric_invocations=0, ROOT_Lean_invocations=0,
        complete_catalogue=False, global_NTT=False, coefficient_N=False, H1=False, D_N=False, WIN=False)
    out = C / 'messages/round22_parameter_guard01_revision02_closed_observation.json'
    with out.open('x', encoding='utf-8') as stream:
        json.dump(observation, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    insight = ('PARAMETER_GUARD01 revision02 actual AUX_PASS : unique parent cf3e25/session93619, '
        'enfant exit0 et5parametres/5logs/4mutants conformes au scopeSOURCE audite ; '
        'ROOT conserve physiquement1005inputs3089archives et original/copie de chaque capture. '
        'Primitives PAPER seulement ;0creditLean, pascatalogue complet/NTT/coefficientN1e8/H1/D_N/WIN. '
        'Ancienguard01 jamais lance et source/gate preserves.')
    helper = r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py'
    result_state = subprocess.run([sys.executable, '-B', '-X', 'utf8', helper, 'record',
        '--cwd', str(B), '--run-name', 'parity', '--node-id', '15.3',
        '--raw-report', insight, '--score', '0', '--insight', insight,
        '--result', 'PARAMETER_GUARD_AUX_PASS_GLOBAL_COEFFICIENT_OPEN', '--no-propagate'],
        capture_output=True, text=True, encoding='utf-8')
    assert result_state.returncode == 0, (result_state.stdout, result_state.stderr)
    cp['previous_goal_turn_evidence'].append(str(out.relative_to(B)))
    cp['last_progress'] = insight
    for actor in cp['in_flight_executors']:
        if actor['role'] == 3:
            actor['status'] = 'ROLE6_PARAMETER_GUARD_REVISION02_CLOSED_AUX_PASS_SOURCE52_SEPARATE'
    cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    with (B / 'REPORT.md').open('a', encoding='utf-8') as stream:
        stream.write('\n' + insight + '\n')
    print(json.dumps(observation, ensure_ascii=False, indent=2))

if __name__ == '__main__':
    main()
