"""Record actual new-bank attempts with pre-execution snapshots; no replay here."""
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


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


parser = argparse.ArgumentParser()
parser.add_argument('bank', choices=['typeii', 'semiprime'])
parser.add_argument('--attempt', type=int, default=1)
args = parser.parse_args()
bank, attempt = args.bank, args.attempt
assert attempt >= 1
prefix = f'{bank}_attempt{attempt:02d}'
source = ROOT / (bank + '_checks.py')
output = ROOT / (bank + '.json')
assert not (ROLE / (bank + '_canonical_receipt.json')).exists(), 'No attempt after canonical PASS'
command = [sys.executable, '-B', '-X', 'utf8', str(source), '--output-dir', str(ROOT)]
started = ROLE / (prefix + '_started.json')
with started.open('x', encoding='utf-8') as handle:
    json.dump({'state': 'PRE_EXECUTION', 'bank': bank, 'attempt': attempt, 'started_at_utc': now(),
               'command': command, 'source_sha256': digest(source),
               'helper_sha256': digest(ROLE / 'strict.py'), 'launcher_sha256': digest(Path(__file__)),
               'protected_registry_sha256': digest(ROOT / 'previous_artifacts_sha256.json')}, handle, indent=2)
    handle.write('\n')
snapshot = ROLE / (prefix + '_source.py.txt')
helper_snapshot = ROLE / (prefix + '_strict.py.txt')
with snapshot.open('xb') as handle:
    handle.write(source.read_bytes())
with helper_snapshot.open('xb') as handle:
    handle.write((ROLE / 'strict.py').read_bytes())
pre = json.loads(started.read_text(encoding='utf-8'))
pre.update({'snapshot_sha256': digest(snapshot), 'helper_snapshot_sha256': digest(helper_snapshot),
            'snapshot_completed_at_utc': now()})
assert pre['snapshot_sha256'] == pre['source_sha256']
assert pre['helper_snapshot_sha256'] == pre['helper_sha256']
save(started, pre)
log = ROLE / (prefix + '.log')
began = time.monotonic()
with log.open('xb') as handle:
    run = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT, check=False)
receipt = {'state': 'FINISHED', 'bank': bank, 'attempt': attempt, 'command': command,
           'started_at_utc': pre['started_at_utc'], 'finished_at_utc': now(),
           'elapsed_seconds': time.monotonic() - began, 'exit_code': run.returncode,
           'source_sha256': pre['source_sha256'], 'source_after_sha256': digest(source),
           'helper_sha256': pre['helper_sha256'], 'helper_after_sha256': digest(ROLE / 'strict.py'),
           'snapshot_sha256': digest(snapshot), 'helper_snapshot_sha256': digest(helper_snapshot),
           'log_sha256': digest(log), 'launcher_sha256': digest(Path(__file__)),
           'protected_registry_sha256': pre['protected_registry_sha256'],
           'old_producer_or_old_Lean_replayed': False, 'victory': False}
assert receipt['source_sha256'] == receipt['source_after_sha256']
assert receipt['helper_sha256'] == receipt['helper_after_sha256']
if run.returncode == 0:
    assert output.exists()
    data = json.loads(output.read_text(encoding='utf-8'))
    assert data['victory'] is False and data['strict_rational_only'] is True
    receipt['output_sha256'] = digest(output)
    receipt['output_status'] = data['status']
    receipt['canonical_pass'] = True
    save(ROLE / (bank + '_canonical_receipt.json'), receipt)
else:
    receipt['canonical_pass'] = False
save(ROLE / (prefix + '_receipt.json'), receipt)
print(json.dumps(receipt, indent=2, ensure_ascii=False))
sys.exit(run.returncode)
