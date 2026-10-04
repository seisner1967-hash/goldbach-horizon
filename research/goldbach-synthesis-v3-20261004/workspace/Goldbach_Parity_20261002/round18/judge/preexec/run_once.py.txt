"""Exclusive execution gate and PREEXEC capture. Presence never authorizes execution."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
import os
import subprocess
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
PYTHON = Path(r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
LEAN = Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
CACHE = BASE.parent / 'q356-canonical-binding-replay/.lake/packages'
LEAN_SHA = '8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
PACKAGES = ['aesop', 'batteries', 'importGraph', 'LeanSearchClient', 'mathlib', 'plausible', 'proofwidgets', 'Qq']


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def exclusive(path, value):
    with Path(path).open('x', encoding='utf-8') as f:
        f.write(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + '\n')


def main():
    authorization_path = HERE / 'authorization.json'
    assert authorization_path.exists(), 'PREPARATION ONLY: separate root authorization absent'
    auth = load(authorization_path)
    assert auth['root_authorized_after_FINAL3_FINAL4_inspection'] is True
    assert auth['role'] == 5 and auth['round'] == 18
    assert set(auth['judge_code_sha256']) == {'audit.py', 'run_once.py'}
    for name, expected in auth['judge_code_sha256'].items():
        assert sha(HERE / name) == expected, ('reviewed judge code changed', name)
    assert not (HERE / 'audit_started.json').exists(), 'an actual audit already started; continuation must preserve PASS stages'
    assert sha(LEAN) == LEAN_SHA
    for rel, expected in auth['FINAL_reports_sha256'].items():
        assert sha(ROUND / rel) == expected, ('FINAL report changed', rel)
    for rel, expected in auth['new_module_sources_sha256'].items():
        assert sha(ROUND / rel) == expected, ('new module changed', rel)
    for rel, expected in auth.get('distinct_final_inputs_sha256', {}).items():
        assert sha(ROUND / rel) == expected, ('distinct FINAL input changed', rel)
    modules = auth['new_module_source_order']
    assert set(modules) == set(auth['new_module_sources_sha256']) and len(modules) == len(set(modules))
    assert len(modules) == 8 and all(Path(p).suffix == '.lean' and Path(p).parts[0] in ('role3', 'role4') for p in modules)
    names = ['PROBE_BLOCK.md', 'previous_artifacts_sha256.json', 'agent1_calibrated_typeii.md',
             'agent2_capacity_incidence.md', 'agent6.md', 'numeric_manifest.json', 'role6_final_receipt.json',
             *auth['FINAL_reports_sha256'], *auth.get('distinct_annex_inputs', [])]
    paths = {ROUND / p for p in names}
    nm = load(ROUND / 'numeric_manifest.json')
    paths.update(ROUND / p for p in nm['sha256'])
    paths.update(ROUND / p for p in load(ROUND / 'role6_final_receipt.json')['sha256'])
    paths.update(p for folder in ('role3', 'role4') for p in (ROUND / folder).rglob('*') if p.is_file())
    for folder in auth.get('distinct_annex_dirs', []):
        assert folder in ('role6_crt', 'role5_content')
        paths.update(p for p in (ROUND / folder).rglob('*') if p.is_file())
    paths.update(ROUND / ('role6/' + p) for p in
                 ('closure_receipt.json', 'finalize_attempt01.log', 'finalize_attempt01_receipt.json'))
    bindings = {p.relative_to(ROUND).as_posix(): sha(p) for p in sorted(paths)}
    historical_dirs = [BASE / 'round17/judge/build', BASE / 'round16/role3',
                       BASE / 'round16/role4', BASE / 'round13/role4/dependencies']
    historical = {p.relative_to(BASE).as_posix(): sha(p) for folder in historical_dirs
                  for p in folder.iterdir() if p.is_file() and p.suffix in ('.olean', '.lean')}
    libs = [CACHE / p / '.lake/build/lib' for p in PACKAGES]
    assert all(p.is_dir() for p in libs) and len(libs) == 8
    mathlib_head = CACHE / 'mathlib/.git/HEAD'
    assert mathlib_head.read_text(encoding='utf-8').strip() == '9837ca9d65d9de6fad1ef4381750ca688774e608'
    snapshots = HERE / 'preexec'
    snapshots.mkdir(exist_ok=False)
    for p in (HERE / 'audit.py', Path(__file__), authorization_path):
        with (snapshots / (p.name + '.txt')).open('xb') as f:
            f.write(p.read_bytes())
    for rel in modules:
        p = ROUND / rel
        with (snapshots / (p.stem + '.lean.txt')).open('xb') as f:
            f.write(p.read_bytes())
    inputs = {'round': 18, 'status': 'FROZEN_ONLY_AFTER_ROOT_AUTHORIZATION',
              'frozen_at_utc': datetime.now(timezone.utc).isoformat(),
              'authorization_sha256': sha(authorization_path), 'round18_sha256': bindings,
              'new_module_sources': modules,
              'distinct_FINAL_inputs_sha256': auth.get('distinct_final_inputs_sha256', {}),
              'author_build_ledgers': sorted(p.relative_to(ROUND).as_posix()
                                            for role in ('role3', 'role4')
                                            for p in (ROUND / role).glob('*build_receipt.json')),
              'historical_dependencies_sha256': historical,
              'historical_library_dirs': list(map(str, historical_dirs)),
              'cache_library_dirs': list(map(str, libs)),
              'mathlib_commit_expected': '9837ca9d65d9de6fad1ef4381750ca688774e608',
              'mathlib_HEAD_path': str(mathlib_head), 'mathlib_HEAD_sha256': sha(mathlib_head),
              'lean_executable': str(LEAN), 'lean_sha256': LEAN_SHA,
              'original_documents_sha256': load(BASE / 'INPUT_HASHES.json'),
              'judge_code_sha256': {p.name: sha(p) for p in (HERE / 'audit.py', Path(__file__))},
              'old_sources_compiled': False, 'author18_oleans_in_Lean_path': False}
    exclusive(HERE / 'input_manifest.json', inputs)
    command = [str(PYTHON), '-B', '-X', 'utf8', str(HERE / 'audit.py')]
    started = {'round': 18, 'status': 'PREEXEC', 'started_at_utc': datetime.now(timezone.utc).isoformat(),
               'command': command, 'cwd': str(HERE), 'input_manifest_sha256': sha(HERE / 'input_manifest.json'),
               'audit_source_sha256': sha(HERE / 'audit.py'), 'launcher_sha256': sha(Path(__file__)),
               'authorization_sha256': sha(authorization_path),
               'audit_snapshot_sha256': sha(snapshots / 'audit.py.txt'),
               'launcher_snapshot_sha256': sha(snapshots / 'run_once.py.txt'),
               'python_sha256': sha(PYTHON)}
    exclusive(HERE / 'audit_started.json', started)
    with (HERE / 'audit.log').open('xb') as f:
        run = subprocess.run(command, cwd=HERE, stdout=f, stderr=subprocess.STDOUT)
    result = dict(started, status='FINISHED', finished_at_utc=datetime.now(timezone.utc).isoformat(),
                  exit_code=run.returncode, log_sha256=sha(HERE / 'audit.log'))
    if (HERE / 'audit_receipt.json').exists():
        result['audit_receipt_sha256'] = sha(HERE / 'audit_receipt.json')
    exclusive(HERE / 'launch_receipt.json', result)
    print(json.dumps({'exit_code': run.returncode, 'log_sha256': result['log_sha256']}), flush=True)
    sys.exit(run.returncode)


if __name__ == '__main__':
    main()
