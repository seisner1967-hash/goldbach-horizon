"""PREEXEC metadata snapshots and actual exit receipt; no math or Lean replay."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write('\n')


def main():
    assert not (HERE / 'closure_receipt.json').exists()
    assert not (HERE / 'final_receipt.json').exists()
    assert (HERE / 'audit_receipt.json').is_file()
    source, launcher = HERE / 'finalize_metadata.py', Path(__file__)
    captures = {}
    for p, name in ((source, 'finalize_attempt01_source.py.txt'),
                    (launcher, 'finalize_attempt01_launcher.py.txt')):
        target = HERE / name
        with target.open('xb') as f:
            f.write(p.read_bytes())
        assert sha(target) == sha(p)
        captures[target.name] = sha(target)
    command = [sys.executable, '-B', '-X', 'utf8', str(source)]
    started = {'status': 'PREEXEC_METADATA_ONLY', 'command': command, 'cwd': str(HERE),
               'started_utc': datetime.now(timezone.utc).isoformat(),
               'source_sha256': sha(source), 'launcher_sha256': sha(launcher), 'captures_sha256': captures,
               'audit_receipt_sha256': sha(HERE / 'audit_receipt.json'),
               'launch_receipt_sha256': sha(HERE / 'launch_receipt.json'),
               'mathematical_expression_or_Lean_to_execute': False, 'victory': False}
    save(HERE / 'finalize_attempt01_started.json', started)
    log = HERE / 'finalize_attempt01.log'
    with log.open('xb') as f:
        run = subprocess.run(command, cwd=HERE, stdout=f, stderr=subprocess.STDOUT)
    receipt = dict(started, status='FINISHED', exit_code=run.returncode,
                   finished_utc=datetime.now(timezone.utc).isoformat(),
                   source_after_sha256=sha(source), launcher_after_sha256=sha(launcher),
                   log_sha256=sha(log), started_sha256=sha(HERE / 'finalize_attempt01_started.json'))
    save(HERE / 'finalize_attempt01_receipt.json', receipt)
    assert sha(source) == started['source_sha256'] and sha(launcher) == started['launcher_sha256']
    if run.returncode == 0:
        files = [HERE / n for n in ('manifest.json', 'final_receipt.json',
                 'finalize_attempt01_started.json', 'finalize_attempt01_receipt.json',
                 'finalize_attempt01.log', 'finalize_metadata.py', 'close_once.py',
                 'finalize_attempt01_source.py.txt', 'finalize_attempt01_launcher.py.txt')]
        files.append(HERE.parent / 'agent5.md')
        save(HERE / 'closure_receipt.json', {'status': 'FINAL5_CLOSED_AFTER_ACTUAL_METADATA_EXIT',
             'metadata_exit_code': run.returncode, 'finished_utc': datetime.now(timezone.utc).isoformat(),
             'bindings_sha256': {p.relative_to(BASE).as_posix(): sha(p) for p in files},
             'audit_or_Lean_stages_replayed': 0, 'numeric_producers_called': 0,
             'score': 0, 'victory': False})
    print(json.dumps({'metadata_exit_code': run.returncode, 'log_sha256': sha(log)}), flush=True)
    return run.returncode


if __name__ == '__main__':
    sys.exit(main())
