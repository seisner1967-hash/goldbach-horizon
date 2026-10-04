"""Capture one real metadata finalization invocation and its actual exit, no numerical producer."""
import sys
sys.dont_write_bytecode = True
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import subprocess

ROLE = Path(__file__).resolve().parent
ROOT = ROLE.parent
SOURCE = ROOT / 'finalize_numeric.py'


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


command = [sys.executable, '-B', '-X', 'utf8', str(SOURCE)]
started = ROLE / 'finalize_attempt01_started.json'
with started.open('x', encoding='utf-8') as handle:
    json.dump({'state': 'PRE_EXECUTION', 'attempt': 1, 'command': command,
               'started_at_utc': datetime.now(timezone.utc).isoformat(),
               'source_sha256': digest(SOURCE), 'launcher_sha256': digest(Path(__file__))}, handle, indent=2)
    handle.write('\n')
snapshot = ROLE / 'finalize_attempt01_source.py.txt'
with snapshot.open('xb') as handle:
    handle.write(SOURCE.read_bytes())
assert digest(snapshot) == digest(SOURCE)
pre = json.loads(started.read_text(encoding='utf-8'))
pre.update({'snapshot_sha256': digest(snapshot), 'snapshot_path': str(snapshot),
            'snapshot_completed_at_utc': datetime.now(timezone.utc).isoformat()})
save(started, pre)
log = ROLE / 'finalize_attempt01.log'
with log.open('xb') as handle:
    run = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT, check=False)
receipt = {'attempt': 1, 'command': command, 'exit_code': run.returncode,
           'source_sha256': digest(SOURCE), 'snapshot_sha256': digest(snapshot), 'log_sha256': digest(log),
           'launcher_sha256': digest(Path(__file__)), 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
           'metadata_collation_only_no_producer_kernel_Lean_or_sign_expression_execution': True}
save(ROLE / 'finalize_attempt01_receipt.json', receipt)
if run.returncode == 0:
    closure = {'round': 18, 'status': 'FINAL6_CLOSURE_AFTER_ACTUAL_EXIT0', 'finalizer_exit_code': 0,
               'report_sha256': digest(ROOT / 'agent6.md'), 'numeric_manifest_sha256': digest(ROOT / 'numeric_manifest.json'),
               'role6_final_receipt_sha256': digest(ROOT / 'role6_final_receipt.json'),
               'finalizer_actual_receipt_sha256': digest(ROLE / 'finalize_attempt01_receipt.json'),
               'finalizer_log_sha256': digest(log), 'finalizer_started_sha256': digest(started),
               'finalizer_source_sha256': digest(SOURCE), 'finalizer_snapshot_sha256': digest(snapshot),
               'finalizer_launcher_sha256': digest(Path(__file__)), 'score': 0, 'victory': False}
    save(ROLE / 'closure_receipt.json', closure)
    print(json.dumps(closure, indent=2, ensure_ascii=False))
else:
    print(json.dumps(receipt, indent=2, ensure_ascii=False))
sys.exit(run.returncode)
