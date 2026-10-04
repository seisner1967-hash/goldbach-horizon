"""Protect all final production through round12; never execute historical banks."""
import sys
sys.dont_write_bytecode=True
from hashlib import sha256
from pathlib import Path
import argparse
import json
import os
import re

ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
CURRENT_ROUND=13
BASELINE=ROOT/'previous_artifacts_sha256.json'
PREVIOUS_BASELINE=BASE/'round12'/'previous_artifacts_sha256.json'
EXPECTED_COUNT=514
EXPECTED_PREVIOUS_COUNT=487
EXPECTED_ROUND12_COUNT=27
EXPECTED_CONTROLLER12='d84cca25948c6794764f3afbc7b6fa23d46faa4152fdad17f2f87da69929a400'
SKIP={'.lake','.git','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}


def excluded_directory(name):
    if name in SKIP:
        return True
    match=re.fullmatch(r'round([0-9]+)',name)
    return bool(match and int(match.group(1))>=CURRENT_ROUND)


def current_records():
    records={}
    for directory,children,files in os.walk(BASE,followlinks=False):
        children[:]=sorted(name for name in children if not excluded_directory(name))
        for name in sorted(files):
            path=Path(directory)/name
            if path==BASE/'REPORT.md':
                continue
            records[path.relative_to(BASE).as_posix()]=sha256(path.read_bytes()).hexdigest()
    return dict(sorted(records.items()))


def source_integrity():
    expected=json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8'))
    result={}
    for name,digest in sorted(expected.items()):
        actual=sha256(Path(name).read_bytes()).hexdigest()
        assert actual==digest,(name,digest,actual)
        result[name]=dict(expected_sha256=digest,actual_sha256=actual,status='PRESERVED')
    assert len(result)==2
    return result


def initialize():
    if not BASELINE.exists():
        records=current_records()
        previous=json.loads(PREVIOUS_BASELINE.read_text(encoding='utf-8'))['sha256']
        assert len(previous)==EXPECTED_PREVIOUS_COUNT
        previous_changes={name:dict(previous=value,current=records.get(name,'MISSING'))
            for name,value in previous.items() if records.get(name)!=value}
        newest_count=sum(name.startswith('round12/') for name in records)
        unrelated_added=sorted(name for name in set(records)-set(previous)
            if not name.startswith('round12/'))
        if len(records)!=EXPECTED_COUNT or newest_count!=EXPECTED_ROUND12_COUNT or previous_changes or unrelated_added:
            diagnostic=dict(status='BASELINE_SCOPE_DISCREPANCY',expected_files=EXPECTED_COUNT,
                actual_files=len(records),expected_round12=EXPECTED_ROUND12_COUNT,
                actual_round12=newest_count,previous_changes=previous_changes,
                unrelated_added=unrelated_added,files=records)
            (ROOT/'baseline_discrepancy.json').write_text(json.dumps(diagnostic,indent=2)+'\n',encoding='utf-8')
            raise AssertionError({k:v for k,v in diagnostic.items() if k!='files'})
        assert records['round12/controller_manifest.json']==EXPECTED_CONTROLLER12
        payload=dict(scope='All final production through round12; sources, logs, PNG, produced olean, Judge and controller12 included; parsed roundNN>=13, caches, .arbor, .git and live REPORT.md excluded',
            last_frozen_round=12,file_count=len(records),round12_file_count=newest_count,
            previous_protected_count=len(previous),previous_baseline_sha256=sha256(PREVIOUS_BASELINE.read_bytes()).hexdigest(),
            original_sources=source_integrity(),sha256=records)
        BASELINE.write_text(json.dumps(payload,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    payload=json.loads(BASELINE.read_text(encoding='utf-8'))
    assert payload['file_count']==len(payload['sha256'])==EXPECTED_COUNT
    assert payload['round12_file_count']==EXPECTED_ROUND12_COUNT and payload['last_frozen_round']==12
    return payload['sha256']


def verify():
    records=initialize();current=current_records()
    changed={name:dict(previous=digest,current=current.get(name,'MISSING'))
        for name,digest in records.items() if current.get(name)!=digest}
    added=sorted(set(current)-set(records))
    assert not changed and not added,dict(changed=changed,added=added)
    assert current['round12/controller_manifest.json']==EXPECTED_CONTROLLER12
    return dict(status='PRESERVED',files=len(records),round12_files=EXPECTED_ROUND12_COUNT,
        previous_protected_files=EXPECTED_PREVIOUS_COUNT,round12_controller_sha256=EXPECTED_CONTROLLER12,
        baseline_sha256=sha256(BASELINE.read_bytes()).hexdigest(),registry=str(BASELINE),
        original_sources=source_integrity())


def output_directory(argument=None):
    directory=(Path(argument) if argument else ROOT).resolve()
    assert directory==ROOT or ROOT in directory.parents,'Output must remain in round13'
    directory.mkdir(parents=True,exist_ok=True)
    return directory


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=ROOT)
    args=parser.parse_args();result=verify()
    (output_directory(args.output_dir)/'conservation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
