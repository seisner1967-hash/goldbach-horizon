"""Freeze round13 only after both explicit FINAL formalist signals."""
import argparse
import json
from hashlib import sha256
from pathlib import Path

JUDGE = Path(__file__).resolve().parent
ROUND = JUDGE.parent
BASE = ROUND.parent
TRUSTED = {
    'agent1_exchange.md': '2b64a5434c1dfde766436d5abd44b62a2714615992193a3f0e21bf90554d8c54',
    'agent2_signed_operator.md': '91946283d4ca1f5021de670b16167e0a0714d0945104d30c4070ca9a26bc9c46',
    'agent6.md': '00e234c7543fbb77d41f3f7d297c15b6bb649b6d940179509f7d916e68bb6bc0',
    'numeric_manifest.json': 'c8468f94a118555c842a47879772620bf9dca9d520a6b89cec54f2895a38f932',
    'previous_artifacts_sha256.json': '02c04c95e5348369b9c4577ac3a14e5b4b89e15f53e142e75a37e58b6bde7351',
}
DEPENDENCIES = [
    ('round10/lean/ShortDivisorComplement.lean', '25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447'),
    ('round11/lean/ThreeAdicPrimePairing.lean', 'b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48'),
]

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

parser = argparse.ArgumentParser()
for role in (3, 4):
    parser.add_argument(f'--role{role}-report', required=True)
    parser.add_argument(f'--role{role}-report-sha', required=True)
    parser.add_argument(f'--role{role}-module-sha', required=True)
args = parser.parse_args()
trusted = dict(TRUSTED)
reports = ['agent1_exchange.md', 'agent2_signed_operator.md', 'agent6.md']
signals = {}
new_modules = ['lean/PrimeSemiprimeSwitch.lean', 'lean/HarmonicKernelVariation.lean']
for role, module in zip((3, 4), new_modules):
    name = getattr(args, f'role{role}_report')
    expected = getattr(args, f'role{role}_report_sha')
    module_sha = getattr(args, f'role{role}_module_sha')
    assert len(expected) == len(module_sha) == 64
    assert sha(ROUND / name) == expected and sha(ROUND / module) == module_sha
    trusted[name] = expected
    reports.append(name)
    signals[f'role{role}'] = dict(terminated=True, report=name,
        report_sha256=expected, module=module, module_sha256=module_sha)
for name, expected in trusted.items():
    assert sha(ROUND / name) == expected, name
numeric = json.loads((ROUND / 'numeric_manifest.json').read_bytes())
assert numeric['status'] == 'FROZEN_NUMERICAL_INPUTS_TERMINATED'
assert numeric['file_count'] == len(numeric['sha256']) == 11
for name, expected in numeric['sha256'].items():
    assert sha(ROUND / name) == expected, name
external = json.loads((BASE / 'INPUT_HASHES.json').read_text(encoding='utf-8'))
for name, expected in DEPENDENCIES:
    path = BASE / name
    assert sha(path) == expected
    external[str(path)] = expected
for name, expected in external.items():
    assert sha(Path(name)) == expected
files = {p.relative_to(ROUND).as_posix(): sha(p) for p in sorted(ROUND.rglob('*'))
         if p.is_file() and 'judge' not in p.relative_to(ROUND).parts
         and '__pycache__' not in p.relative_to(ROUND).parts and p.name != 'agent5.md'}
payload = dict(round=13, status='FINAL_INPUTS_FROZEN', reports=reports,
    final_role_signals=signals, new_lean_sources=new_modules,
    dependency_sources=[str(BASE / name) for name, _ in DEPENDENCIES],
    dependency_expected_conclusions={'ShortDivisorComplement': 17, 'ThreeAdicPrimePairing': 19},
    file_count=len(files), sha256=files, external_sha256=external,
    numeric_manifest_sha256=TRUSTED['numeric_manifest.json'],
    old_artifacts=514, previous_auxiliary_modules=13, previous_auxiliary_conclusions=169)
path = JUDGE / 'input_sha256.json'
path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=payload['status'], files=len(files), reports=len(reports),
                     manifest_sha256=sha(path)), indent=2))
