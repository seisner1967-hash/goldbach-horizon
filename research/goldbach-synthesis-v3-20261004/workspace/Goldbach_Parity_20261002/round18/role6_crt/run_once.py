"""Exclusive PREEXEC capture and actual subprocess receipt for NEW CRT only.

Requires a distinct root authorization for canonical and isolated replay.
Never imports a mathematical producer and never reruns an existing PASS.
"""
import sys
sys.dont_write_bytecode = True
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time

ROLE = Path(__file__).resolve().parent


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write('\n')


def copy_exclusive(source, destination):
    with Path(destination).open('xb') as handle:
        handle.write(Path(source).read_bytes())
    assert digest(source) == digest(destination)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('kind', choices=['canonical', 'replay'])
    parser.add_argument('--attempt', type=int, default=1)
    args = parser.parse_args()
    assert args.attempt > 0
    if args.kind == 'canonical':
        assert not (ROLE / 'canonical_receipt.json').exists(), 'Canonical PASS is frozen'
        label = f'canonical_attempt{args.attempt:02d}'
    else:
        assert args.attempt == 1 and (ROLE / 'canonical_receipt.json').is_file()
        assert not (ROLE / 'replay_receipt.json').exists(), 'Only one isolated replay'
        label = 'replay_attempt01'
    reviewed = ['crt_checks.py', 'crt_helpers.py', 'run_once.py',
                'contract.json', 'input_registry.json']
    reviewed_sha = {name: digest(ROLE / name) for name in reviewed}
    authorization_path = ROLE / f'{args.kind}_authorization.json'
    authorization = json.loads(authorization_path.read_text(encoding='utf-8'))
    assert authorization['root_authorized'] is True
    assert authorization['kind'] == args.kind and authorization['attempt'] == args.attempt
    assert authorization['reviewed_sha256'] == reviewed_sha
    contract = json.loads((ROLE / 'contract.json').read_text(encoding='utf-8'))
    assert contract['input_registry_sha256'] == reviewed_sha['input_registry.json']
    bindings = json.loads((ROLE / 'input_registry.json').read_text(encoding='utf-8'))
    for binding in bindings['inputs'].values():
        assert digest(binding['path']) == binding['sha256'], binding['path']
    canonical = None
    if args.kind == 'replay':
        canonical = json.loads((ROLE / 'canonical_receipt.json').read_text(encoding='utf-8'))
        assert canonical['exit_code'] == 0 and canonical['canonical_pass'] is True
        assert canonical['reviewed_sha256'] == reviewed_sha
        assert digest(canonical['output']) == canonical['output_sha256']
        assert authorization['canonical_receipt_sha256'] == digest(ROLE / 'canonical_receipt.json')
        assert authorization['canonical_output_sha256'] == canonical['output_sha256']
    # Every new directory, snapshot, marker, log and receipt is exclusive.
    work = ROLE / label
    work.mkdir()
    captures = {}
    for name in reviewed:
        destination = work / (name if name in ['crt_checks.py', 'crt_helpers.py']
                              else name + '.txt')
        copy_exclusive(ROLE / name, destination)
        captures[str(destination)] = digest(destination)
    inputs_dir = work / 'inputs'
    inputs_dir.mkdir()
    for name, binding in bindings['inputs'].items():
        destination = inputs_dir / (name + Path(binding['path']).suffix + '.txt')
        copy_exclusive(binding['path'], destination)
        captures[str(destination)] = digest(destination)
    authorization_copy = work / 'authorization.json.txt'
    copy_exclusive(authorization_path, authorization_copy)
    captures[str(authorization_copy)] = digest(authorization_copy)
    command = [sys.executable, '-B', '-X', 'utf8', str(work / 'crt_checks.py'),
               '--contract', str(ROLE / 'contract.json'), '--output-dir', str(work)]
    started_path = ROLE / (label + '_started.json')
    started = {'state': 'PRE_EXECUTION', 'round': 18, 'role': '6_CRT_annex',
               'kind': args.kind, 'attempt': args.attempt,
               'captured_at_utc': now(), 'command': command, 'cwd': str(work),
               'reviewed_sha256': reviewed_sha,
               'authorization_sha256': digest(authorization_path),
               'input_bindings': bindings['inputs'], 'capture_sha256': captures,
               'subprocess_not_started_when_capture_written': True,
               'old_producers_or_banks_replayed': False, 'victory': False}
    save(started_path, started)
    log = ROLE / (label + '.log')
    began = time.monotonic()
    began_at = now()
    launch_error = None
    run = None
    with log.open('xb') as handle:
        try:
            run = subprocess.run(command, cwd=work, stdout=handle,
                                 stderr=subprocess.STDOUT, check=False)
        except Exception as error:
            launch_error = repr(error)
            handle.write((launch_error + '\n').encode('utf-8'))
    after_sha = {name: digest(ROLE / name) for name in reviewed}
    input_after_sha = {name: digest(binding['path']) for name, binding in bindings['inputs'].items()}
    receipt = {'state': 'FINISHED' if run is not None else 'LAUNCH_FAILED',
               'round': 18, 'role': '6_CRT_annex', 'kind': args.kind,
               'attempt': args.attempt, 'command': command, 'cwd': str(work),
               'started_at_utc': began_at, 'finished_at_utc': now(),
               'elapsed_seconds': time.monotonic() - began,
               'actual_subprocess_returned': run is not None,
               'exit_code': run.returncode if run is not None else None,
               'launch_error': launch_error,
               'reviewed_sha256': reviewed_sha, 'source_after_sha256': after_sha,
               'input_bindings': bindings['inputs'], 'input_after_sha256': input_after_sha,
               'capture_sha256': captures, 'started_sha256': digest(started_path),
               'authorization_sha256': digest(authorization_path),
               'log_sha256': digest(log), 'canonical_pass': False,
               'old_producers_or_banks_replayed': False,
               'W_D_kernel_called': False, 'existing_log_sign_recomputed': False,
               'Lean_called': False, 'score': 0, 'victory': False}
    output = work / 'crt.json'
    validation_error = None
    try:
        assert after_sha == reviewed_sha
        assert all(input_after_sha[name] == binding['sha256']
                   for name, binding in bindings['inputs'].items())
        if run is not None and run.returncode == 0:
            result = json.loads(output.read_text(encoding='utf-8'))
            assert result['status'] == 'PASS_NEW_CRT_FULL_DIVISORS_IE_AND_GUARDED_FRONTS'
            assert result['strict_integer_rational_only'] is True and result['victory'] is False
            receipt.update({'output': str(output), 'output_sha256': digest(output),
                            'output_status': result['status']})
            if args.kind == 'canonical':
                receipt['canonical_pass'] = True
            else:
                expected = Path(canonical['output']).read_bytes()
                actual = output.read_bytes()
                assert actual == expected and result == json.loads(expected.decode('utf-8'))
                receipt.update({'byte_identical_to_canonical': True,
                                'field_identical_to_canonical': True,
                                'canonical_output_sha256': canonical['output_sha256'],
                                'canonical_receipt_sha256': digest(ROLE / 'canonical_receipt.json')})
    except Exception as error:
        validation_error = repr(error)
        receipt['canonical_pass'] = False
    receipt['post_execution_validation_error'] = validation_error
    if validation_error is None and run is not None and run.returncode == 0:
        save(ROLE / ('canonical_receipt.json' if args.kind == 'canonical' else 'replay_receipt.json'), receipt)
    save(ROLE / (label + '_receipt.json'), receipt)
    print(json.dumps(receipt, indent=2, sort_keys=True, ensure_ascii=False))
    if run is None:
        raise RuntimeError('New CRT subprocess launch failed: ' + launch_error)
    if validation_error is not None:
        raise RuntimeError('Post-execution CRT validation failed: ' + validation_error)
    return run.returncode


if __name__ == '__main__':
    sys.exit(main())
