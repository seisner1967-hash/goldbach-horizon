"""Freeze final role inputs only after receiving explicit final role3/4 signals."""
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
    'agent1_prime_signed.md': 'e439a43eea07380643c233ca6e48442d79e0c6cd1bdff4d67adc590797791064',
    'agent2_prime_operator.md': '55b0eddd21732a6d9052f888d6df7114c4041ad41e8e59c33c6568bab261b4fa',
    'agent6.md': '3453e489eb94df5a187b107173a9081c95471116ae0369de4dd3d0d1cb7ef413',
    'paired_cofactor_checks.py': 'bdee7952e47419fef2a0512d8e74a7234bf3da6800e2dc9561b94f9bd34d5ef2',
    'paired_cofactors.json': '909df1b5cd38a4ed42cad65ca8930c47930d7ba8afd356148d87f4c7edcf34b2',
    'witness_search.py': '3ac3774c25997c8a59c13862ada7b843bb19f7dd178bba0b45d0d5be5ddd28bb',
    'witnesses.json': '527df6b3bc8a71cdbf6e76b428b048d13c8cf6af764f94d0fb7b94a5f008d598',
    'shared.py': '1c49e5abc36ceacfd65e8fc7ca97cee1705a60e693870b6e4942091ba2a1d868',
    'conservation.py': '6b27a617019d937fd4c40d243b0173240984d126ecd377d15cbf2b9934cc7254',
    'previous_artifacts_sha256.json': '39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb',
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

parser = argparse.ArgumentParser()
for role in ['3', '4']:
    parser.add_argument('--role' + role + '-report', required=True)
    parser.add_argument('--role' + role + '-report-sha', required=True)
    parser.add_argument('--role' + role + '-module-sha', required=True)
args = parser.parse_args()
signals = {}
for role, module in [('3', 'PrimeCofactorIdentity'), ('4', 'ShortDivisorComplement')]:
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
        authorization='Explicit TERMINÉ + final SHA received from completed role')
for relative, expected in EXPECTED.items():
    assert sha(ROUND / relative) == expected, relative
# Preserve final production logs and snapshots as evidence; never use their oleans to compile.
records = {}
for path in sorted(ROUND.rglob('*')):
    if not path.is_file() or JUDGE in path.parents or '__pycache__' in path.parts:
        continue
    if path.name == 'agent5.md':
        continue
    records[path.relative_to(ROUND).as_posix()] = sha(path)
assert all(records[name] == digest for name, digest in EXPECTED.items())
external = json.loads((BASE / 'INPUT_HASHES.json').read_text(encoding='utf-8'))
for absolute, expected in external.items():
    assert sha(Path(absolute)) == expected, absolute
payload = dict(round=10, role_reports=5, numerical_sources=2,
    final_role_signals=signals,
    new_lean_sources=['lean/PrimeCofactorIdentity.lean', 'lean/ShortDivisorComplement.lean'],
    sha256=records, external_sha256=external,
    source_onset='u>=10^24', previous_artifacts=341,
    snapshot_scope='All existing final round10 production outside judge and agent5; final role signals required')
destination = JUDGE / 'input_sha256.json'
destination.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status='FINAL_INPUTS_FROZEN', files=len(records),
    role_reports=5, new_lean_sources=2, manifest_sha256=sha(destination)), indent=2))
