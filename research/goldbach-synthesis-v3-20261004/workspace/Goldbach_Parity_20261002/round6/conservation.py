"""Round 6 baseline of frozen earlier sources, scripts, receipts and builders."""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from pathlib import Path
import json
import os

ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
BASELINE=ROOT/'previous_artifacts_sha256.json'
SUFFIXES={'.lean','.py','.ps1','.json','.toml','.txt','.log','.md'}
SKIP={'.lake','.git','.arbor','__pycache__','round6'}


def initialize():
    if not BASELINE.exists():
        records={}
        for directory,children,files in os.walk(BASE,followlinks=False):
            children[:]=[name for name in children if name not in SKIP]
            for name in files:
                path=Path(directory)/name
                if path==BASE/'REPORT.md' or path.suffix.lower() not in SUFFIXES:
                    continue
                records[path.relative_to(BASE).as_posix()]=sha256(path.read_bytes()).hexdigest()
        BASELINE.write_text(json.dumps(dict(scope='Earlier local artifacts; live central report, controller state and dependency caches excluded',
                                           file_count=len(records),sha256=dict(sorted(records.items()))),indent=2)+'\n',encoding='utf-8')
    return json.loads(BASELINE.read_text(encoding='utf-8'))['sha256']


def verify():
    records=initialize()
    changed={}
    for relative,digest in records.items():
        path=BASE/relative
        current=sha256(path.read_bytes()).hexdigest() if path.exists() else 'MISSING'
        if current!=digest:
            changed[relative]=dict(previous=digest,current=current)
    assert not changed,changed
    return dict(status='PRESERVED',files=len(records),baseline_sha256=sha256(BASELINE.read_bytes()).hexdigest())


if __name__=='__main__':
    result=verify()
    (ROOT/'conservation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
