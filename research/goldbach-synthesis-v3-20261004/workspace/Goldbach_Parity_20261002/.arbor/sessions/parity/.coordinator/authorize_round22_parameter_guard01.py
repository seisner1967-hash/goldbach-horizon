"""ROOT metadata gate only. No candidate import, mathematics, compiler or child."""
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C = B / '.arbor/sessions/parity/.coordinator'
PACK = B / 'round22/role4/parameter_guard01'
PYTHON = Path(r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
PYTHON_SHA = '4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'

def sha(path):
    result = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1048576), b''):
            result.update(data)
    return result.hexdigest()

def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--review-path', required=True)
    parser.add_argument('--review-sha', required=True)
    parser.add_argument('--ROOT-full-read-receipts', required=True)
    args = parser.parse_args()
    review = Path(args.review_path).resolve()
    assert review.is_relative_to((B / 'round22/judge5').resolve())
    assert sha(review) == args.review_sha
    prep_path = PACK / 'preparation22.json'
    assert sha(prep_path) == '418654b335c4e26043b1262eb371a2517e3bcde39db470190f5a25320a88a3bc'
    prep = read(prep_path)
    assert prep['scope'] == 'PARAMETER_GUARD01_ONLY'
    assert prep['status'] == 'SOURCE_METADATA_PREPARED_WAITING_INDEPENDENT_REVIEW_AND_ROOT_GATE'
    assert prep['binding_count'] == 998
    assert prep['max_children'] == 1 and prep['max_retries'] == 0
    assert prep['wall_seconds'] == 60 and prep['output_bytes'] == 1048576
    assert prep['new_numeric_runs'] == 0 and prep['candidate_imports'] == 0
    assert not prep['NTT_global'] and not prep['coefficient_N'] and not prep['WIN']
    assert Path(prep['canonical_python']).resolve() == PYTHON.resolve()
    assert sha(PYTHON) == PYTHON_SHA
    manifest_path = Path(prep['manifest_path']).resolve()
    assert manifest_path == (PACK / 'prepared_manifest22.json').resolve()
    assert sha(manifest_path) == prep['manifest_sha256'] == '6e9db8525d2467c941fdc0dad85ccd5bcec7556fa49cf0368ef4052e223018d2'
    bindings = read(manifest_path)['bindings']
    assert len(bindings) == 998
    seen = set()
    for row in bindings:
        path = Path(row['path']).resolve()
        key = str(path).casefold()
        assert key not in seen
        seen.add(key)
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], str(path)
    required_files = [PACK / name for name in ('parameter_guard22.py', 'run_parameter_guard_once22.py', 'contract22.md', 'read_receipts22.json')]
    required_files += [B / 'round22/role4/circle_ntt_paper01/fixed_parameter_log_model22.py', PYTHON]
    assert all(str(path.resolve()).casefold() in seen for path in required_files)
    handoff_path = B / 'round22/role4/circle_ntt_paper01/source_handoff22.json'
    assert sha(handoff_path) == 'fbbf4bef50bae5fb9de72e2bb923a3fbc0cfc03982a26abf2bb6f889002a1eab'
    old = read(handoff_path)['bindings']
    assert len(old) == 19
    for row in old:
        assert sha(Path(row['path'])) == row['sha256'], row['path']
    registry_path = B / 'round22/previous_artifacts_sha256.json'
    assert sha(registry_path) == '875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99'
    registry = read(registry_path)
    assert registry['file_count'] == len(registry['sha256']) == 3089
    for relative, expected in registry['sha256'].items():
        path = (B / relative).resolve()
        assert path.is_relative_to(B.resolve()) and sha(path) == expected, relative
    assert not (PACK / 'actual_attempt01').exists(), 'No rerun or start replay'
    cp_path = C / 'checkpoint.json'
    cp = read(cp_path)
    gate = {
        'schema': 'ROUND22_ROOT_PARAMETER_GUARD01_AUTHORIZATION',
        'time_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'AUTHORIZED', 'scope': 'PARAMETER_GUARD01_ONLY',
        'preparation_sha256': sha(prep_path), 'source_manifest_sha256': sha(manifest_path),
        'max_children': 1, 'max_retries': 0, 'wall_seconds': 60, 'output_bytes': 1048576,
        'independent_source_review_path': str(review), 'independent_source_review_sha256': args.review_sha,
        'executor_role': 'ROLE6', 'executor_actor': '/root/round22_formal3_prepare',
        'canonical_python': str(PYTHON), 'python_sha256': PYTHON_SHA,
        'ROOT_full_read_receipts': args.ROOT_full_read_receipts,
        'bindings_verified': 998, 'old_NTT_bindings_verified': 19, 'protected_archives_verified': 3089,
        'sources_and_tools_verified': {str(path): sha(path) for path in required_files},
        'read_scope': 'Tool/contract/review FULL; large manifest every entry parsed and every byte hash-verified, no raw FULL claim',
        'official_credit_added': 0,
        'official_modules_before_gate': cp['official_auxiliary_validation']['modules'],
        'official_declarations_before_gate': cp['official_auxiliary_validation']['declarations'],
        'ROOT_numeric_invocations': 0, 'ROOT_Lean_invocations': 0,
        'coefficient_N_evaluation_authorized': False, 'native_build_authorized': False,
        'NTT_global_authorized': False, 'new_Lean_invocation_authorized': False,
        'log_primitive_Lean_certified': False, 'H1_paid': False, 'D_N_paid': False, 'WIN': False,
    }
    gate_path = C / 'messages/round22_parameter_guard01_authorization.json'
    with gate_path.open('x', encoding='utf-8') as stream:
        json.dump(gate, stream, ensure_ascii=False, indent=2)
        stream.write('\n')
    cp['previous_goal_turn_evidence'].append(str(gate_path.relative_to(B)))
    for actor in cp['in_flight_executors']:
        if actor['role'] == 3:
            actor['status'] = 'ROLE6_PARAMETER_GUARD01_AUTHORIZED_PENDING_START_SOURCE_WORK_SEPARATE'
    cp_path.write_text(json.dumps(cp, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    with (B / 'REPORT.md').open('a', encoding='utf-8') as stream:
        stream.write('\nPARAMETER_GUARD01 : gate ROOT distincte après revue indépendante SOURCE,998bindings/19anciensNTT/3089archives conservés. Unique futur enfant ROLE6,60s/1MiB/0retry, seuls paramètres et5échantillons de log ; aucune NTT globale/coefficientN/build natif/Lean autorisés. Aucun résultat numérique anticipé, H1/D_N/WIN ouverts.\n')
    print(json.dumps({'gate': str(gate_path), 'gate_sha256': sha(gate_path), 'metadata_only': True}))

if __name__ == '__main__':
    main()
