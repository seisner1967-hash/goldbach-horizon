"""Independent read-only final inputs and exact historical inventory verifier."""
import sys
sys.dont_write_bytecode = True
import json, os, re
from hashlib import sha256
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
REGISTRY_SHA = '310e5f7df62b7f67fa29302f2eb634a740da6f979ce8c23f0a4415941b075407'
CONTROLLER_SHA = '64417450e8b96dfdd562765d4919d27d2e8ba98919ff79ac806d94d10bdd201d'
SKIP = {'.lake', '.git', '.arbor', '__pycache__', '.pytest_cache', '.mypy_cache', '.ruff_cache'}
def digest(p): return sha256(p.read_bytes()).hexdigest()
def verify_inputs(inputs):
    assert inputs['round'] == 14 and inputs['status'] == 'FINAL_INPUTS_FROZEN'
    assert inputs['file_count'] == len(inputs['sha256'])
    assert len(inputs['reports']) == 3 and all(v['terminated'] for v in inputs['final_role_signals'].values())
    for name, expected in inputs['sha256'].items(): assert digest(ROUND / name) == expected, name
    for name, expected in inputs['external_sha256'].items(): assert digest(Path(name)) == expected, name
def preservation(inputs):
    registry_path = ROUND / 'previous_artifacts_sha256.json'
    assert digest(registry_path) == REGISTRY_SHA
    registry = json.loads(registry_path.read_bytes())
    assert registry['file_count'] == len(registry['sha256']) == 603
    assert registry['last_frozen_round'] == 13 and registry['round13_file_count'] == 89
    current = {}
    for directory, children, files in os.walk(BASE, followlinks=False):
        def excluded(name):
            match = re.fullmatch(r'round([0-9]+)', name)
            return name in SKIP or bool(match and int(match.group(1)) >= 14)
        children[:] = sorted(n for n in children if not excluded(n))
        for name in sorted(files):
            path = Path(directory) / name
            if path != BASE / 'REPORT.md': current[path.relative_to(BASE).as_posix()] = digest(path)
    assert current == registry['sha256'], 'Protected files changed, disappeared or were added'
    assert current['round13/controller_manifest.json'] == CONTROLLER_SHA
    assert sum(n.startswith('round13/') for n in current) == 89
    ctrl = json.loads((BASE / 'round13/controller_manifest.json').read_bytes())
    assert ctrl['round'] == 13 and ctrl['score'] == 0 and ctrl['victory'] is False
    assert len(ctrl['bindings_sha256']) == 88
    for name, expected in ctrl['bindings_sha256'].items():
        assert current['round13/' + name] == expected
    sources = {n: dict(expected_sha256=h, actual_sha256=digest(Path(n))) for n,h in inputs['external_sha256'].items()}
    assert all(v['expected_sha256'] == v['actual_sha256'] for v in sources.values())
    return dict(status='PRESERVED', files=603, previous_protected_files=514, round13_files=89,
        controller13_sha256=CONTROLLER_SHA, controller_bindings=88, registry_sha256=REGISTRY_SHA,
        exact_inventory_additions_and_removals_checked=True, original_sources=sources)
if __name__ == '__main__':
    inputs = json.loads((HERE / 'input_sha256.json').read_bytes())
    verify_inputs(inputs)
    print(json.dumps(preservation(inputs), indent=2))
