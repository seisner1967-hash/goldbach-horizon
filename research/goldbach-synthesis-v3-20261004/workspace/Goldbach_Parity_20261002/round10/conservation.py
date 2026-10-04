"""Full round10 production registry; rounds >=10 are outside frozen scope."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import re

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
CURRENT_ROUND = 10
BASELINE = ROOT / 'previous_artifacts_sha256.json'
SKIP = {'.lake', '.git', '.arbor', '__pycache__', '.pytest_cache',
        '.mypy_cache', '.ruff_cache'}
EXPECTED_CONTROLLER9 = 'ef316624b2c49ee3689de9ce24cbf9ecb531fc05e913760341118c47afc334d3'


def excluded_directory(name):
    if name in SKIP:
        return True
    match = re.fullmatch(r'round([0-9]+)', name)
    return bool(match and int(match.group(1)) >= CURRENT_ROUND)


def current_records():
    records = {}
    for directory, children, files in os.walk(BASE, followlinks=False):
        children[:] = sorted(name for name in children if not excluded_directory(name))
        for name in sorted(files):
            path = Path(directory) / name
            if path == BASE / 'REPORT.md':
                continue
            records[path.relative_to(BASE).as_posix()] = sha256(path.read_bytes()).hexdigest()
    return dict(sorted(records.items()))


def source_integrity():
    expected = json.loads((BASE / 'INPUT_HASHES.json').read_text(encoding='utf-8'))
    result = {}
    for name, digest in sorted(expected.items()):
        actual = sha256(Path(name).read_bytes()).hexdigest()
        assert actual == digest, (name, digest, actual)
        result[name] = dict(expected_sha256=digest, actual_sha256=actual, status='PRESERVED')
    assert len(result) == 2
    return result


def initialize():
    if not BASELINE.exists():
        records = current_records()
        assert records['round9/controller_manifest.json'] == EXPECTED_CONTROLLER9
        payload = dict(
            scope='All protected production through completed round9, including PNG, produced olean and round9/controller_manifest.json; parsed roundNN>=10, dependency caches, .arbor, .git and live central REPORT.md excluded',
            last_frozen_round=9,
            file_count=len(records),
            round9_file_count=sum(name.startswith('round9/') for name in records),
            original_sources=source_integrity(),
            sha256=records,
        )
        BASELINE.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
    payload = json.loads(BASELINE.read_text(encoding='utf-8'))
    assert payload['file_count'] == len(payload['sha256'])
    assert payload['last_frozen_round'] == 9
    return payload['sha256']


def verify():
    records = initialize()
    current = current_records()
    changed = {
        name: dict(previous=digest, current=current.get(name, 'MISSING'))
        for name, digest in records.items() if current.get(name) != digest
    }
    added = sorted(set(current) - set(records))
    assert not changed and not added, dict(changed=changed, added=added)
    assert current['round9/controller_manifest.json'] == EXPECTED_CONTROLLER9
    return dict(status='PRESERVED', files=len(records),
                round9_files=sum(name.startswith('round9/') for name in records),
                round9_controller_sha256=EXPECTED_CONTROLLER9,
                baseline_sha256=sha256(BASELINE.read_bytes()).hexdigest(),
                registry=str(BASELINE), original_sources=source_integrity())


def output_directory(argument=None):
    directory = (Path(argument) if argument else ROOT).resolve()
    assert directory == ROOT or ROOT in directory.parents, 'Output must remain in round10'
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
