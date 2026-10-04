"""Read-only byte verification of already-read FINAL1/FINAL2; metadata only."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
import json
from datetime import datetime, timezone
B = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R = B / 'round19'
C = B / '.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_bytes())
def digest(p): return sha256(p.read_bytes()).hexdigest()
def check(p, spec):
    data = p.read_bytes()
    assert sha256(data).hexdigest() == spec['sha256'], str(p)
    assert len(data) == spec['bytes'], str(p)
expected = {
    'agent1_weighted_aggregate.md': 'd1cd64e27c46ad5aacfe2ee33c1b13681b77ae84e6d78c8585a3ef47acaf42bb',
    'role1/manifest.json': '77a7b1c481b146f3c2787e27effc9b6e68b99c1beb4d8b6866ae613311fb3104',
    'role1/final_receipt.json': '99a76bc309945c02a051d6943b9e82f098fdd24da3043dfdeedf310026ad0eb6',
    'agent2_nonss.md': '20ca15ceba20b72459102b2da8429b7e6d72a7c4bd52dca7de7bc3a58a61cbc2',
    'role2/test_contract.json': '29c4474d148a6e8cbe3a431130cc9143af2efc277682f4c38b5e5be99bb06037',
    'role2/manifest.json': '66a5e12172d93ccbc4460bf5733a81c284aeb101976f9319c7fc1909ad449252',
    'role2/final_receipt.json': '6081619ec9d4c942b24cb5fbd72b9ee316712d99b61a5503a98c83790f2df1d0',
}
out = C / 'messages/round19_ideations_root_observation.json'
assert not out.exists(), 'No repeat of successful metadata verification'
for rel, h in expected.items(): assert digest(R / rel) == h, rel
m1, m2 = read(R / 'role1/manifest.json'), read(R / 'role2/manifest.json')
for rel, spec in m1['bindings'].items(): check(B / rel, spec)
for rel, spec in m2['owned'].items(): check(R / rel, spec)
for absolute, spec in m2['readonly_inputs'].items(): check(Path(absolute), spec)
f1, f2 = read(R / 'role1/final_receipt.json'), read(R / 'role2/final_receipt.json')
assert f1['manifest_sha256'] == expected['role1/manifest.json']
assert f1['report_sha256'] == expected['agent1_weighted_aggregate.md']
assert f1['bound_files'] == len(m1['bindings']) == 12
assert f2['manifest_sha256'] == expected['role2/manifest.json']
assert f2['report']['sha256'] == expected['agent2_nonss.md']
assert f2['contract']['sha256'] == expected['role2/test_contract.json']
assert len(m2['owned']) == f2['owned_bindings'] == 2
assert len(m2['readonly_inputs']) == f2['readonly_bindings'] == 9
assert not f1['victory'] and not f2['victory']
pre = read(C / 'messages/round19_conservation_root_observation.json')
assert pre['status'] == 'ROOT_VERIFIED_ACTUAL_UNIQUE_CONSERVATION19'
observation = dict(status='ROOT_FULL_READ_AND_BYTE_VERIFIED_FINAL1_FINAL2_19',
    observed_utc=datetime.now(timezone.utc).isoformat(), report_receipt_hashes=expected,
    role1_bindings_verified=12, role2_owned_verified=2, role2_readonly_verified=9,
    mathematics_executed=0, Lean_invocations=0, numerical_producers=0,
    role1_contract_location='agent1_weighted_aggregate.md section11 (no standalone test_contract.json)',
    root_read_incident='One absent role1/test_contract.json lookup: read-only missing path, not a mathematical failure; contract is fully read in report.',
    source_guards=['u>=10^24 unchanged', 'rank price only canonical extraction15',
      'P=1771 requires gcd(P,N)=1', 'Gamma_rank remains unpaid', 'BV onset not computed',
      'nonSS balanced conductor<N, not necessarily<=sqrtN',
      'rank3 short bound conditional and onset1e40, source gap remains',
      'all long/medium/rank>=4 prices and entire ledger remain unpaid'], victory=False)
out.write_text(json.dumps(observation, indent=2, ensure_ascii=False)+'\n', encoding='utf-8')
print('FINAL1/2 fully read; 23 metadata bindings and seven final hashes verified; no math/Lean/producer executed; noWin')
