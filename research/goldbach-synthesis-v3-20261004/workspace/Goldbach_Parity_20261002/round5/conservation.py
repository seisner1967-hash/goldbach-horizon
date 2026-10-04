"""SHA256 baseline for frozen earlier task artifacts; outputs round5 only."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from pathlib import Path
import json
import os

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent
BASELINE = ROOT/'previous_artifacts_sha256.json'
SUFFIXES = {'.lean','.py','.ps1','.json','.toml','.txt','.log','.md'}
SKIP_DIRS = {'.lake','.git','.arbor','__pycache__','round5'}


def hashes():
    result = {}
    for directory,children,files in os.walk(BASE,followlinks=False):
        children[:] = [name for name in children if name not in SKIP_DIRS]
        for name in files:
            path = Path(directory)/name
            # REPORT.md is the live central report. Earlier per-round
            # reports, sources, receipts and builders are included.
            if path == BASE/'REPORT.md' or path.suffix.lower() not in SUFFIXES:
                continue
            result[path.relative_to(BASE).as_posix()] = sha256(path.read_bytes()).hexdigest()
    return dict(sorted(result.items()))


def initialize():
    if not BASELINE.exists():
        snapshot = hashes()
        BASELINE.write_text(json.dumps(dict(scope='Earlier local sources/scripts/receipts/builders; live root REPORT.md, controller state, dependency caches excluded',
                                           file_count=len(snapshot),sha256=snapshot),indent=2)+'\n',encoding='utf-8')
    return json.loads(BASELINE.read_text(encoding='utf-8'))['sha256']


def verify():
    previous = initialize()
    changed = {}
    for relative,digest in previous.items():
        path = BASE/relative
        observed = sha256(path.read_bytes()).hexdigest() if path.exists() else 'MISSING'
        if observed != digest:
            changed[relative] = dict(previous=digest,observed=observed)
    assert not changed, changed
    return dict(status='PRESERVED',files=len(previous),
                baseline_sha256=sha256(BASELINE.read_bytes()).hexdigest())


if __name__ == '__main__':
    initialize()
    print(json.dumps(verify(),indent=2))
