"""Capture exactly one real conservation invocation; never launch old mathematics."""
import sys
sys.dont_write_bytecode = True
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import time

ROLE = Path(__file__).resolve().parent
ROOT = ROLE.parent
SOURCE = ROOT / 'conservation.py'


def digest(path):
    h = sha256()
    with Path(path).open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


ROLE.mkdir(parents=True, exist_ok=True)
snapshot = ROLE / 'conservation_attempt01_source.py.txt'
log = ROLE / 'conservation_attempt01.log'
receipt = ROLE / 'conservation_attempt01_receipt.json'
started = ROLE / 'conservation_attempt01_started.json'
command = [sys.executable, '-B', '-X', 'utf8', str(SOURCE), '--output-dir', str(ROOT)]
with started.open('x', encoding='utf-8') as handle:
    json.dump({'state': 'PRE_EXECUTION', 'attempt': 1, 'started_at_utc': now(),
               'command': command, 'source_sha256': digest(SOURCE),
               'launcher_sha256': digest(Path(__file__)),
               'previous_registry_sha256': digest(ROOT / 'previous_artifacts_sha256.json'),
               'snapshot_pending': True}, handle, indent=2)
    handle.write('\n')
with snapshot.open('xb') as handle:
    handle.write(SOURCE.read_bytes())
assert digest(snapshot) == digest(SOURCE)
pre_execution = json.loads(started.read_text(encoding='utf-8'))
pre_execution.update({'snapshot': str(snapshot), 'snapshot_sha256': digest(snapshot),
                      'snapshot_pending': False, 'snapshot_completed_at_utc': now()})
save(started, pre_execution)
began = time.monotonic()
with log.open('xb') as handle:
    run = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT, check=False)
result = {'attempt': 1, 'state': 'FINISHED', 'command': command,
          'started_at_utc': pre_execution['started_at_utc'], 'finished_at_utc': now(),
          'elapsed_seconds': time.monotonic() - began, 'exit_code': run.returncode,
          'source_sha256_before_execution': pre_execution['source_sha256'],
          'source_sha256_after_execution': digest(SOURCE),
          'snapshot': str(snapshot), 'snapshot_sha256': digest(snapshot),
          'log': str(log), 'log_sha256': digest(log),
          'launcher_sha256': digest(Path(__file__)),
          'no_old_mathematical_producer_or_compiler_launched': True,
          'new_numeric_bank_selected': False, 'mathematical_victory_claim': False}
if (ROOT / 'conservation.json').exists():
    result['conservation_sha256'] = digest(ROOT / 'conservation.json')
if (ROOT / 'conservation_failure.json').exists():
    result['failure_sha256'] = digest(ROOT / 'conservation_failure.json')
save(receipt, result)
print(json.dumps(result, indent=2, ensure_ascii=False))
sys.exit(run.returncode)
