"""Freeze round14 production only after explicit FINAL2 and FINAL6 signals."""
import sys
sys.dont_write_bytecode = True
import argparse, json
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent
TRUSTED = {
    'agent1_coverage.md': '4224fdd0f202da0a1dae1787965cb24aaeb7cf88fbcba8e92f607aff98716aec',
    'previous_artifacts_sha256.json': '310e5f7df62b7f67fa29302f2eb634a740da6f979ce8c23f0a4415941b075407',
    'role6_final_receipt.json': '0cb35796d1b790b46a27a193b2f79280015b1c1f59b0150801447c4240834b3d',
}
def digest(p): return sha256(p.read_bytes()).hexdigest()
parser = argparse.ArgumentParser()
parser.add_argument('--role2-sha', required=True)
parser.add_argument('--role6-sha', required=True)
parser.add_argument('--numeric-manifest-sha', required=True)
args = parser.parse_args()
signals = {'role1': {'terminated': True, 'report': 'agent1_coverage.md', 'report_sha256': TRUSTED['agent1_coverage.md']}}
for role, name, expected in ((2, 'agent2_complement.md', args.role2_sha), (6, 'agent6.md', args.role6_sha)):
    assert len(expected) == 64 and digest(ROUND / name) == expected, name
    TRUSTED[name] = expected
    signals[f'role{role}'] = {'terminated': True, 'report': name, 'report_sha256': expected}
TRUSTED['numeric_manifest.json'] = args.numeric_manifest_sha
for name, expected in TRUSTED.items(): assert digest(ROUND / name) == expected, name
numeric = json.loads((ROUND / 'numeric_manifest.json').read_bytes())
assert numeric['status'] == 'FROZEN_NUMERICAL_INPUTS_TERMINATED'
assert numeric['file_count'] == len(numeric['sha256']) == 32
assert numeric['final_conceptual_report_sha256'] == {n:TRUSTED[n] for n in ('agent1_coverage.md','agent2_complement.md')}
required = {'conservation.py', 'shared.py', 'coverage_checks.py', 'complement_checks.py',
    'coverage_pair_supplement.py', 'coverage.json', 'complement.json',
    'coverage_pair_supplement.json', 'numerical_replay.json', 'previous_artifacts_sha256.json', 'agent6.md'}
assert required <= set(numeric['sha256'])
for name, expected in numeric['sha256'].items(): assert digest(ROUND / name) == expected, name
external = json.loads((BASE / 'INPUT_HASHES.json').read_text(encoding='utf-8'))
assert len(external) == 2
for name, expected in external.items(): assert digest(Path(name)) == expected, name
files = {p.relative_to(ROUND).as_posix(): digest(p) for p in sorted(ROUND.rglob('*'))
    if p.is_file() and 'judge' not in p.relative_to(ROUND).parts
    and '__pycache__' not in p.relative_to(ROUND).parts and p.name != 'agent5.md'}
assert not any(n.endswith('.lean') for n in files), 'Unexpected new Lean proposal; stop for semantic review'
payload = dict(round=14, status='FINAL_INPUTS_FROZEN', reports=[v['report'] for v in signals.values()],
    final_role_signals=signals, file_count=len(files), sha256=files, external_sha256=external,
    numeric_manifest_sha256=args.numeric_manifest_sha, old_artifacts=603,
    cumulative_auxiliary_modules=15, cumulative_auxiliary_conclusions=208)
dest = HERE / 'input_sha256.json'
assert not dest.exists(), 'Inputs already frozen'
dest.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print(json.dumps(dict(status=payload['status'], files=len(files), reports=len(signals), sha256=digest(dest)), indent=2))
