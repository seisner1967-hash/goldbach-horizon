"""Exactly one explicitly authorized isolated new-round18 replay per bank."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
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
    h = sha256()
    with Path(path).open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def now():
    return datetime.now(timezone.utc).isoformat()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


parser = argparse.ArgumentParser()
parser.add_argument('bank', choices=['typeii', 'semiprime'])
args = parser.parse_args()
bank = args.bank
canonical = ROOT / (bank + '.json')
canonical_receipt = ROLE / (bank + '_canonical_receipt.json')
certificate = json.loads(canonical_receipt.read_text(encoding='utf-8'))
assert certificate['exit_code'] == 0 and certificate['canonical_pass'] is True
assert digest(canonical) == certificate['output_sha256']
sources = [ROOT / (bank + '_checks.py'), ROLE / 'strict.py']
if bank == 'semiprime':
    sources.append(ROLE / 'semiprime_helpers.py')
    canonical_bindings = certificate['sources_before_sha256']
    assert certificate['sources_after_sha256'] == canonical_bindings
else:
    canonical_bindings = {bank + '_checks.py': certificate['source_sha256'],
                          'role6/strict.py': certificate['helper_sha256']}
for p in sources:
    assert digest(p) == canonical_bindings[p.relative_to(ROOT).as_posix()]
registry = ROOT / 'previous_artifacts_sha256.json'
assert digest(registry) == '05212665afffecade91134e1533f93d11eba8058179198e4420eef1fe252f2bc'
capture = sources + [Path(__file__).resolve(), registry]
bindings = {p.relative_to(ROOT).as_posix(): digest(p) for p in capture}
out = (ROOT / ('isolated_' + bank)).resolve()
assert ROOT in out.parents and not out.exists(), 'isolated directory must be entirely new'
command = [sys.executable, '-B', '-X', 'utf8', str(sources[0]), '--output-dir', str(out)]
started = ROLE / (bank + '_replay_started.json')
with started.open('x', encoding='utf-8') as handle:
    json.dump({'state': 'PRE_EXECUTION', 'bank': bank, 'attempt': 1,
               'authorized_distinct_replay': True, 'started_at_utc': now(), 'command': command,
               'source_helper_launcher_registry_sha256': bindings,
               'canonical_output_sha256': digest(canonical),
               'canonical_receipt_sha256': digest(canonical_receipt)}, handle, indent=2)
    handle.write('\n')
snapdir = ROLE / (bank + '_replay_snapshots')
snapdir.mkdir(exist_ok=False)
snapshots = {}
for p in capture:
    name = p.relative_to(ROOT).as_posix().replace('/', '__') + '.txt'
    snapshot = snapdir / name
    with snapshot.open('xb') as handle:
        handle.write(p.read_bytes())
    assert digest(snapshot) == bindings[p.relative_to(ROOT).as_posix()]
    snapshots[snapshot.relative_to(ROOT).as_posix()] = digest(snapshot)
pre = json.loads(started.read_text(encoding='utf-8'))
pre.update({'snapshots_sha256': snapshots, 'snapshot_completed_at_utc': now()})
save(started, pre)
out.mkdir(exist_ok=False)
log = ROLE / (bank + '_replay.log')
began = time.monotonic()
with log.open('xb') as handle:
    run = subprocess.run(command, cwd=out, stdout=handle, stderr=subprocess.STDOUT, check=False)
receipt = {'bank': bank, 'attempt': 1, 'state': 'FINISHED', 'command': command,
           'started_at_utc': pre['started_at_utc'], 'finished_at_utc': now(),
           'elapsed_seconds': time.monotonic() - began, 'exit_code': run.returncode,
           'source_helper_launcher_registry_sha256_before': bindings,
           'source_helper_launcher_registry_sha256_after': {p.relative_to(ROOT).as_posix(): digest(p) for p in capture},
           'snapshots_sha256': snapshots, 'log_sha256': digest(log),
           'canonical_output_sha256_before': pre['canonical_output_sha256'],
           'canonical_output_sha256_after': digest(canonical),
           'canonical_receipt_sha256_before': pre['canonical_receipt_sha256'],
           'canonical_receipt_sha256_after': digest(canonical_receipt),
           'old_rounds1_through17_producer_kernel_sign_or_Lean_replayed': False,
           'explicitly_authorized_new_round18_replay': True, 'victory': False}
check_exit = run.returncode
assert receipt['source_helper_launcher_registry_sha256_before'] == receipt['source_helper_launcher_registry_sha256_after']
assert receipt['canonical_output_sha256_before'] == receipt['canonical_output_sha256_after']
assert receipt['canonical_receipt_sha256_before'] == receipt['canonical_receipt_sha256_after']
if run.returncode == 0:
    replay = out / (bank + '.json')
    receipt['output_sha256'] = digest(replay)
    receipt['bytes_identical'] = canonical.read_bytes() == replay.read_bytes()
    receipt['all_fields_identical'] = json.loads(canonical.read_text(encoding='utf-8')) == json.loads(replay.read_text(encoding='utf-8'))
    receipt['status'] = 'PASS_UNIQUE_ISOLATED_REPLAY' if receipt['bytes_identical'] and receipt['all_fields_identical'] else 'FAILED_ISOLATED_COMPARISON'
    if receipt['status'] != 'PASS_UNIQUE_ISOLATED_REPLAY':
        check_exit = 1
else:
    receipt['status'] = 'FAILED_UNIQUE_ISOLATED_REPLAY_NO_RETRY'
receipt['comparison_exit_code'] = check_exit
save(ROLE / (bank + '_replay_receipt.json'), receipt)
print(json.dumps(receipt, indent=2, ensure_ascii=False))
sys.exit(check_exit)
