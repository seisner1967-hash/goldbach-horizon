"""Independent round15 read-only frozen input and historical inventory verifier."""
import sys
sys.dont_write_bytecode = True
import json, os, re
from hashlib import sha256
from pathlib import Path
HERE=Path(__file__).resolve().parent; ROUND=HERE.parent; BASE=ROUND.parent
REGISTRY_SHA='d43941b27a4325a841282d389476c9c6fa9af920138b9b0deebe1c484a4ff7f4'
CONTROLLER_SHA='6795b8ed10872337ac8d0f7caf7ef428b8611b6f35376e575c22661ff68e30bf'
SKIP={'.lake','.git','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}
def digest(p): return sha256(p.read_bytes()).hexdigest()
def verify_inputs(inputs):
    assert inputs['round']==15 and inputs['status']=='FINAL_INPUTS_FROZEN'
    assert inputs['file_count']==len(inputs['sha256'])
    assert len(inputs['reports'])==3 and all(v['terminated'] for v in inputs['final_role_signals'].values())
    for n,h in inputs['sha256'].items(): assert digest(ROUND/n)==h,n
    for n,h in inputs['external_sha256'].items(): assert digest(Path(n))==h,n
def preservation(inputs):
    p=ROUND/'previous_artifacts_sha256.json'; assert digest(p)==REGISTRY_SHA
    registry=json.loads(p.read_bytes())
    assert registry['file_count']==len(registry['sha256'])==651
    assert registry['last_frozen_round']==14 and registry['round14_file_count']==48
    current={}
    for directory,children,files in os.walk(BASE,followlinks=False):
        def excluded(n):
            match=re.fullmatch(r'round([0-9]+)',n)
            return n in SKIP or bool(match and int(match.group(1))>=15)
        children[:]=sorted(n for n in children if not excluded(n))
        for n in sorted(files):
            p=Path(directory)/n
            if p!=BASE/'REPORT.md': current[p.relative_to(BASE).as_posix()]=digest(p)
    assert current==registry['sha256'],'Protected inventory changed, disappeared or was added'
    assert current['round14/controller_manifest.json']==CONTROLLER_SHA
    assert sum(n.startswith('round14/') for n in current)==48
    ctrl=json.loads((BASE/'round14/controller_manifest.json').read_bytes())
    assert ctrl['round']==14 and ctrl['score']==0 and ctrl['victory'] is False
    assert len(ctrl['bindings_sha256'])==47
    for n,h in ctrl['bindings_sha256'].items(): assert current['round14/'+n]==h,n
    originals={n:dict(expected_sha256=h,actual_sha256=digest(Path(n))) for n,h in inputs['external_sha256'].items()}
    assert all(v['expected_sha256']==v['actual_sha256'] for v in originals.values())
    return dict(status='PRESERVED',files=651,previous_protected_files=603,round14_files=48,
        controller14_sha256=CONTROLLER_SHA,controller_bindings=47,registry_sha256=REGISTRY_SHA,
        exact_inventory_additions_and_removals_checked=True,original_sources=originals)
if __name__=='__main__':
    inputs=json.loads((HERE/'input_sha256.json').read_bytes()); verify_inputs(inputs)
    print(json.dumps(preservation(inputs),indent=2))
