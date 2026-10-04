"""Freeze only explicitly FINAL round12 inputs; execute no arithmetic producer."""
import argparse
import json
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
TRUSTED = {
    'agent2_bilateral.md': '71e8b1fb2d7a4d20d146e4357ea0a6ab5f7c1fd0af77d1386db50dbaf5ecd91a',
    'agent6.md': 'ee2383547abc96817911f7120e09246a2d36e579e940004cd8d2062688198759',
    'numeric_manifest.json': 'e6c7321c0584827e72e1850f0053018b598e35229bc818affaf1b83462198592',
    'previous_artifacts_sha256.json': '9a0a1010cdc4ad16eeb28b15f960f1d7dd3621bc91cc4d241a8781ccc2e543b1',
}

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

parser = argparse.ArgumentParser()
parser.add_argument('--role1-final-sha', required=True)
args = parser.parse_args()
assert len(args.role1_final_sha) == 64
trusted = dict(TRUSTED, **{'agent1_compensation.md': args.role1_final_sha})
for name, expected in trusted.items():
    assert digest(ROUND / name) == expected, name
numeric = json.loads((ROUND / 'numeric_manifest.json').read_bytes())
assert numeric['status'] == 'FROZEN_NUMERICAL_INPUTS_TERMINATED'
assert numeric['file_count'] == len(numeric['sha256']) == 13
for name, expected in numeric['sha256'].items():
    assert digest(ROUND / name) == expected, name
files = {p.relative_to(ROUND).as_posix(): digest(p)
         for p in sorted(ROUND.rglob('*')) if p.is_file()
         and 'juge' not in p.relative_to(ROUND).parts
         and '__pycache__' not in p.relative_to(ROUND).parts
         and p.name != 'agent5.md'}
assert not any(name.endswith(('.lean', '.olean')) for name in files)
external = json.loads((ROUND.parent / 'INPUT_HASHES.json').read_text(encoding='utf-8'))
for name, expected in external.items():
    assert digest(Path(name)) == expected, name
payload = dict(round=12, status='FINAL_INPUTS_FROZEN',
    final_role_signals={'role1': dict(terminated=True, report_sha256=args.role1_final_sha),
                       'role2': dict(terminated=True, report_sha256=trusted['agent2_bilateral.md']),
                       'role6': dict(terminated=True, report_sha256=trusted['agent6.md'])},
    reports=['agent1_compensation.md', 'agent2_bilateral.md', 'agent6.md'],
    file_count=len(files), sha256=files, external_sha256=external,
    numeric_manifest_sha256=trusted['numeric_manifest.json'],
    previous_registry_sha256=trusted['previous_artifacts_sha256.json'],
    old_artifacts=487, lean_invoked=False, new_lean_conclusions=0)
output = HERE / 'input_sha256.json'
output.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=payload['status'], files=len(files), reports=3,
                     manifest_sha256=digest(output)), indent=2))
