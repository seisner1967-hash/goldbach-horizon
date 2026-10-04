"""Round 9 frozen production registry; all earlier rounds are read-only."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
BASELINE = ROOT / 'previous_artifacts_sha256.json'
SKIP = {'.lake', '.git', '.arbor', '__pycache__', '.pytest_cache',
        '.mypy_cache', '.ruff_cache', 'round9'}


def current_records():
    records = {}
    for directory, children, files in os.walk(BASE, followlinks=False):
        children[:] = sorted(name for name in children if name not in SKIP)
        for name in sorted(files):
            path = Path(directory) / name
            if path == BASE / 'REPORT.md':
                continue
            records[path.relative_to(BASE).as_posix()] = sha256(path.read_bytes()).hexdigest()
    return dict(sorted(records.items()))


def initialize():
    if not BASELINE.exists():
        records = current_records()
        payload = dict(
            scope='All earlier production files, including every round8 file, PNG and produced olean; round9, dependency caches, .arbor, .git and live central REPORT.md excluded',
            file_count=len(records),
            round8_file_count=sum(path.startswith('round8/') for path in records),
            sha256=records,
        )
        BASELINE.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    payload = json.loads(BASELINE.read_text(encoding='utf-8'))
    assert payload['file_count'] == len(payload['sha256'])
    return payload['sha256']


def verify():
    records = initialize()
    current = current_records()
    changed = {
        path: dict(previous=digest, current=current.get(path, 'MISSING'))
        for path, digest in records.items() if current.get(path) != digest
    }
    added = sorted(set(current) - set(records))
    assert not changed and not added, dict(changed=changed, added=added)
    return dict(status='PRESERVED', files=len(records),
                round8_files=sum(path.startswith('round8/') for path in records),
                baseline_sha256=sha256(BASELINE.read_bytes()).hexdigest(),
                registry=str(BASELINE))


def output_directory(argument=None):
    directory = (Path(argument) if argument else ROOT).resolve()
    assert directory == ROOT or ROOT in directory.parents, 'Output must remain in round9'
    directory.mkdir(parents=True, exist_ok=True)
    return directory


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', type=Path, default=ROOT)
    args = parser.parse_args()
    result = verify()
    destination = output_directory(args.output_dir) / 'conservation.json'
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))
