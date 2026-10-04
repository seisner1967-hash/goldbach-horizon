"""Freeze round11 only after both formalists have delivered final SHA signals."""
import sys
sys.dont_write_bytecode = True
import argparse
import hashlib
import json
from pathlib import Path

JUDGE = Path(__file__).resolve().parent
ROUND = JUDGE.parent
BASE = ROUND.parent
EXPECTED = {
    'agent1_signed_compensation.md': '41cf2ead5d3cb8aa399bfc148e1e29f0f543135ca8b225b0d92c7fb2253ed7dd',
    'agent2_bilateral_compensation.md': 'ea3d4944f5a55df6eb9bbc30fed1fb90a00d24b2c505d196d8b61559394e9830',
    'agent6.md': '59fb6c45d119542d4b364809b3850d1515814b5890bc5a6ec9b67d59d2c55cd7',
    'numeric_manifest.json': 'cf00e641312588a0ab8d9e410f005585bb3e00a0b30b8cee54ba0c1fe7a113c1',
    'previous_artifacts_sha256.json': 'f86a31f72d624124338afad6932cd859dceae164a6f3422f9b8998164fcf9e05',
}
DEPENDENCY = BASE / 'round10' / 'lean' / 'ShortDivisorComplement.lean'
DEPENDENCY_SHA = '25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

parser = argparse.ArgumentParser()
for role in ['3', '4']:
    parser.add_argument('--role' + role + '-report', required=True)
    parser.add_argument('--role' + role + '-report-sha', required=True)
    parser.add_argument('--role' + role + '-module-sha', required=True)
args = parser.parse_args()
signals = {}
for role, module in [('3', 'SquarefreeLcmCoefficient'), ('4', 'ThreeAdicPrimePairing')]:
    report = getattr(args, 'role' + role + '_report')
    digest = getattr(args, 'role' + role + '_report_sha')
    source = 'lean/' + module + '.lean'
    source_digest = getattr(args, 'role' + role + '_module_sha')
    assert (ROUND / report).resolve().parent == ROUND
    assert len(digest) == len(source_digest) == 64
    EXPECTED[report] = digest
    EXPECTED[source] = source_digest
    signals[role] = dict(completed=True, report=report, report_sha256=digest,
        module=source, module_sha256=source_digest,
        authorization='Explicit TERMINÉ and SHA received from completed role')
for relative, expected in EXPECTED.items():
    assert sha(ROUND / relative) == expected, relative
numeric_manifest = json.loads((ROUND / 'numeric_manifest.json').read_text(encoding='utf-8'))
assert numeric_manifest['status'] == 'FROZEN_NUMERICAL_INPUTS_TERMINATED'
assert len(numeric_manifest['sha256']) == numeric_manifest['file_count'] == 14
for relative, expected in numeric_manifest['sha256'].items():
    assert sha(ROUND / relative) == expected, relative
assert sha(DEPENDENCY) == DEPENDENCY_SHA
records = {}
for path in sorted(ROUND.rglob('*')):
    if not path.is_file() or JUDGE in path.parents or '__pycache__' in path.parts:
        continue
    if path.name == 'agent5.md':
        continue
    records[path.relative_to(ROUND).as_posix()] = sha(path)
assert all(records[name] == digest for name, digest in EXPECTED.items())
external = json.loads((BASE / 'INPUT_HASHES.json').read_text(encoding='utf-8'))
external[str(DEPENDENCY)] = DEPENDENCY_SHA
for absolute, expected in external.items():
    assert sha(Path(absolute)) == expected, absolute
payload = dict(round=11, role_reports=5, numerical_sources=3,
    final_role_signals=signals,
    new_lean_sources=['lean/SquarefreeLcmCoefficient.lean', 'lean/ThreeAdicPrimePairing.lean'],
    dependency_sources=[str(DEPENDENCY)],
    dependency_new_results=0, dependency_existing_theorems=17,
    sha256=records, external_sha256=external,
    source_onset='u>=10^24', previous_artifacts=405,
    snapshot_scope='All final round11 production outside judge and agent5; both final formalist signals required')
destination = JUDGE / 'input_sha256.json'
destination.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status='FINAL_INPUTS_FROZEN', files=len(records), role_reports=5,
    new_lean_sources=2, dependency_sources=1, manifest_sha256=sha(destination)), indent=2))
