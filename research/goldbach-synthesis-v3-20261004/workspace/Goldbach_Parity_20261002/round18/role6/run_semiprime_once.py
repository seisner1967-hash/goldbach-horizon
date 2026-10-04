"""SS-specific new-bank invocation, snapshots include its new helper and frozen strict.py."""
import sys
sys.dont_write_bytecode = True
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import argparse
import json
import subprocess
import time

ROLE = Path(__file__).resolve().parent
ROOT = ROLE.parent
SOURCE = ROOT / 'semiprime_checks.py'


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


def now():
    return datetime.now(timezone.utc).isoformat()


parser = argparse.ArgumentParser()
parser.add_argument('--attempt', type=int, default=1)
args = parser.parse_args()
assert args.attempt >= 1
assert not (ROLE / 'semiprime_canonical_receipt.json').exists(), 'No new run after canonical PASS'
prefix = f'semiprime_attempt{args.attempt:02d}'
sources = [SOURCE, ROLE / 'semiprime_helpers.py', ROLE / 'strict.py']
command = [sys.executable, '-B', '-X', 'utf8', str(SOURCE), '--output-dir', str(ROOT)]
started = ROLE / (prefix + '_started.json')
bindings = {str(p.relative_to(ROOT).as_posix()): digest(p) for p in sources}
with started.open('x', encoding='utf-8') as handle:
    json.dump({'state': 'PRE_EXECUTION', 'attempt': args.attempt, 'started_at_utc': now(),
               'command': command, 'sources_sha256': bindings,
               'launcher_sha256': digest(Path(__file__)),
               'protected_registry_sha256': digest(ROOT / 'previous_artifacts_sha256.json')}, handle, indent=2)
    handle.write('\n')
snapshots = {}
for p in sources:
    snapshot = ROLE / (prefix + '_' + p.name + '.txt')
    with snapshot.open('xb') as handle:
        handle.write(p.read_bytes())
    assert digest(snapshot) == bindings[p.relative_to(ROOT).as_posix()]
    snapshots[snapshot.relative_to(ROOT).as_posix()] = digest(snapshot)
pre = json.loads(started.read_text(encoding='utf-8'))
pre.update({'snapshots_sha256': snapshots, 'snapshot_completed_at_utc': now()})
save(started, pre)
log = ROLE / (prefix + '.log')
began = time.monotonic()
with log.open('xb') as handle:
    result = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT, check=False)
receipt = {'attempt': args.attempt, 'state': 'FINISHED', 'bank': 'semiprime', 'command': command,
           'started_at_utc': pre['started_at_utc'], 'finished_at_utc': now(),
           'elapsed_seconds': time.monotonic() - began, 'exit_code': result.returncode,
           'sources_before_sha256': bindings,
           'sources_after_sha256': {p.relative_to(ROOT).as_posix(): digest(p) for p in sources},
           'snapshots_sha256': snapshots, 'log_sha256': digest(log),
           'launcher_sha256': digest(Path(__file__)), 'protected_registry_sha256': pre['protected_registry_sha256'],
           'old_producer_or_old_kernel_or_old_Lean_replayed': False, 'victory': False}
assert receipt['sources_before_sha256'] == receipt['sources_after_sha256']
if result.returncode == 0:
    output = ROOT / 'semiprime.json'
    data = json.loads(output.read_text(encoding='utf-8'))
    assert data['strict_rational_only'] is True and data['victory'] is False
    receipt.update({'output_sha256': digest(output), 'output_status': data['status'], 'canonical_pass': True})
    save(ROLE / 'semiprime_canonical_receipt.json', receipt)
else:
    receipt['canonical_pass'] = False
save(ROLE / (prefix + '_receipt.json'), receipt)
print(json.dumps(receipt, indent=2, ensure_ascii=False))
sys.exit(result.returncode)
