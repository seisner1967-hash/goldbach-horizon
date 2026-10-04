"""Protect all completed production through round11, without running old banks."""
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
CURRENT_ROUND=12
BASELINE=ROOT/'previous_artifacts_sha256.json'
PREVIOUS_BASELINE=BASE/'round11'/'previous_artifacts_sha256.json'
EXPECTED_COUNT=487
EXPECTED_ROUND11_COUNT=82
EXPECTED_CONTROLLER11='3860be999898b537fda692534cbf1943225a7aa65e3bb182b48476a5933dd000'
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
        previous_changes={name:dict(previous=value,current=records.get(name,'MISSING'))
            for name,value in previous.items() if records.get(name)!=value}
        round11_count=sum(name.startswith('round11/') for name in records)
        unrelated_added=sorted(name for name in set(records)-set(previous)
            if not name.startswith('round11/'))
        if len(records)!=EXPECTED_COUNT or round11_count!=EXPECTED_ROUND11_COUNT or previous_changes or unrelated_added:
            diagnostic=dict(status='BASELINE_SCOPE_DISCREPANCY',expected_files=EXPECTED_COUNT,
                actual_files=len(records),expected_round11=EXPECTED_ROUND11_COUNT,
                actual_round11=round11_count,previous_changes=previous_changes,
                unrelated_added=unrelated_added,files=records)
            (ROOT/'baseline_discrepancy.json').write_text(json.dumps(diagnostic,indent=2)+'\n',encoding='utf-8')
            raise AssertionError({k:v for k,v in diagnostic.items() if k!='files'})
        assert records['round11/controller_manifest.json']==EXPECTED_CONTROLLER11
        payload=dict(scope='All completed production through round11; includes original protected production, Judge, sources, logs, PNG, produced olean and controller11; parsed roundNN>=12, caches, .arbor, .git and live REPORT.md excluded',
            last_frozen_round=11,file_count=len(records),round11_file_count=round11_count,
            previous_protected_count=len(previous),previous_baseline_sha256=sha256(PREVIOUS_BASELINE.read_bytes()).hexdigest(),
            original_sources=source_integrity(),sha256=records)
        BASELINE.write_text(json.dumps(payload,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    payload=json.loads(BASELINE.read_text(encoding='utf-8'))
    assert payload['file_count']==len(payload['sha256'])==EXPECTED_COUNT
    assert payload['round11_file_count']==EXPECTED_ROUND11_COUNT and payload['last_frozen_round']==11
    return payload['sha256']


def verify():
    records=initialize();current=current_records()
    changed={name:dict(previous=digest,current=current.get(name,'MISSING'))
        for name,digest in records.items() if current.get(name)!=digest}
    added=sorted(set(current)-set(records))
    assert not changed and not added,dict(changed=changed,added=added)
    assert current['round11/controller_manifest.json']==EXPECTED_CONTROLLER11
    return dict(status='PRESERVED',files=len(records),round11_files=EXPECTED_ROUND11_COUNT,
        previous_protected_files=405,round11_controller_sha256=EXPECTED_CONTROLLER11,
        baseline_sha256=sha256(BASELINE.read_bytes()).hexdigest(),registry=str(BASELINE),
        original_sources=source_integrity())


def output_directory(argument=None):
    directory=(Path(argument) if argument else ROOT).resolve()
    assert directory==ROOT or ROOT in directory.parents,'Output must remain in round12'
    directory.mkdir(parents=True,exist_ok=True)
    return directory


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output-dir',type=Path,default=ROOT)
    args=parser.parse_args();result=verify()
    (output_directory(args.output_dir)/'conservation.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
