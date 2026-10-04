"""Independent read-only protection verifier; no producer or Lean calls."""
import sys
sys.dont_write_bytecode=True
import json,os,re
from hashlib import sha256
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROUND=HERE.parent;BASE=ROUND.parent
REGISTRY_SHA='5939d791139dbb3f9b26e5d1f372bbdf98d1927f9aaf2c5e9c22aa0a4e35d043'
CONTROLLER_SHA='7b2522fbeec0c17965b9bfba4df418552f0e31b2b4881c91edff00b79a81869f'
SKIP={'.lake','.git','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}
def digest(p):return sha256(Path(p).read_bytes()).hexdigest()
def verify_inputs(inputs):
    assert inputs['round']==16 and inputs['status']=='FINAL_INPUTS_FROZEN'
    assert inputs['file_count']==len(inputs['sha256'])
    assert len(inputs['reports'])==5 and all(v['terminated'] for v in inputs['final_role_signals'].values())
    for n,h in inputs['sha256'].items():assert digest(ROUND/n)==h,n
    for n,h in inputs['external_sha256'].items():assert digest(Path(n))==h,n
def preservation(inputs):
    registry_path=ROUND/'previous_artifacts_sha256.json';assert digest(registry_path)==REGISTRY_SHA
    registry=json.loads(registry_path.read_bytes())
    assert registry['file_count']==len(registry['sha256'])==701 and registry['last_frozen_round']==15
    current={}
    for directory,children,files in os.walk(BASE,followlinks=False):
        def excluded(n):
            match=re.fullmatch(r'round([0-9]+)',n)
            return n in SKIP or bool(match and int(match.group(1))>=16)
        children[:]=sorted(n for n in children if not excluded(n))
        for n in sorted(files):
            p=Path(directory)/n
            if p!=BASE/'REPORT.md':current[p.relative_to(BASE).as_posix()]=digest(p)
    assert current==registry['sha256'],'Historical inventory changed, removed or augmented'
    assert current['round15/controller_manifest.json']==CONTROLLER_SHA
    assert sum(n.startswith('round15/') for n in current)==50
    controller=json.loads((BASE/'round15/controller_manifest.json').read_bytes())
    assert controller['round']==15 and controller['score']==0 and controller['victory'] is False
    assert len(controller['bindings_sha256'])==49
    for n,h in controller['bindings_sha256'].items():assert current['round15/'+n]==h,n
    originals={n:dict(expected_sha256=h,actual_sha256=digest(n)) for n,h in inputs['external_sha256'].items()}
    assert all(v['expected_sha256']==v['actual_sha256'] for v in originals.values())
    return dict(status='PRESERVED',files=701,previous_protected_files=651,round15_files=50,
        registry_sha256=REGISTRY_SHA,controller15_sha256=CONTROLLER_SHA,controller_bindings=49,
        exact_inventory_additions_and_removals_checked=True,original_sources=originals)
