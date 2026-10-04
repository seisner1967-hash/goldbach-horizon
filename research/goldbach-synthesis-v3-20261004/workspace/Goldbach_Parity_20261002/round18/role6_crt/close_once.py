"""Once-only metadata finalizer receipt; no mathematical helper imported."""
import sys
sys.dont_write_bytecode = True
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import time

ROLE = Path(__file__).resolve().parent
ROOT = ROLE.parent.parent


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write('\n')


def now():
    return datetime.now(timezone.utc).isoformat()


def main():
    assert not (ROLE / 'closure_receipt.json').exists()
    assert not (ROLE / 'final_receipt.json').exists()
    assert (ROLE / 'canonical_receipt.json').is_file()
    assert not (ROLE / 'replay_receipt.json').exists()
    assert not (ROLE / 'replay_authorization.json').exists()
    source = ROLE / 'finalize_metadata.py'
    launcher = Path(__file__).resolve()
    source_copy = ROLE / 'finalize_attempt01_source.py.txt'
    launcher_copy = ROLE / 'finalize_attempt01_launcher.py.txt'
    for original, copy in [(source, source_copy), (launcher, launcher_copy)]:
        with copy.open('xb') as handle:
            handle.write(original.read_bytes())
        assert digest(original) == digest(copy)
    command = [sys.executable, '-B', '-X', 'utf8', str(source)]
    started_path = ROLE / 'finalize_attempt01_started.json'
    started = {'state': 'PRE_EXECUTION_METADATA_ONLY', 'command': command,
               'cwd': str(ROLE), 'started_at_utc': now(),
               'source_sha256': digest(source), 'source_snapshot_sha256': digest(source_copy),
               'launcher_sha256': digest(launcher), 'launcher_snapshot_sha256': digest(launcher_copy),
               'canonical_receipt_sha256': digest(ROLE / 'canonical_receipt.json'),
               'isolated_replays': 0, 'replay_authorized': False,
               'mathematical_expression_or_old_PASS_to_execute': False, 'victory': False}
    save(started_path, started)
    log = ROLE / 'finalize_attempt01.log'
    began = time.monotonic()
    with log.open('xb') as handle:
        run = subprocess.run(command, cwd=ROLE, stdout=handle, stderr=subprocess.STDOUT, check=False)
    receipt_path = ROLE / 'finalize_attempt01_receipt.json'
    receipt = {**started, 'state': 'FINISHED', 'exit_code': run.returncode,
               'finished_at_utc': now(), 'elapsed_seconds': time.monotonic() - began,
               'source_after_sha256': digest(source), 'launcher_after_sha256': digest(launcher),
               'started_sha256': digest(started_path), 'log_sha256': digest(log),
               'actual_metadata_subprocess_returned': True, 'victory': False}
    save(receipt_path, receipt)
    assert receipt['source_after_sha256'] == started['source_sha256']
    assert receipt['launcher_after_sha256'] == started['launcher_sha256']
    if run.returncode == 0:
        files = [ROLE / name for name in ['manifest.json', 'final_receipt.json',
                 'finalize_attempt01_receipt.json', 'finalize_attempt01.log',
                 'finalize_attempt01_started.json', 'finalize_metadata.py', 'close_once.py',
                 'finalize_attempt01_source.py.txt', 'finalize_attempt01_launcher.py.txt']]
        files.append(ROLE.parent / 'agent6_crt.md')
        closure = {'state': 'FINAL6CRT_CLOSED_AFTER_ACTUAL_METADATA_EXIT',
                   'metadata_exit_code': run.returncode, 'finished_at_utc': now(),
                   'bindings_sha256': {str(path.relative_to(ROOT)): digest(path) for path in files},
                   'numeric_processes_rerun_by_closure': 0, 'new_log_sign_positions': 0,
                   'score': 0, 'victory': False}
        save(ROLE / 'closure_receipt.json', closure)
    print(json.dumps(receipt, indent=2, sort_keys=True, ensure_ascii=False))
    return run.returncode


if __name__ == '__main__':
    sys.exit(main())
