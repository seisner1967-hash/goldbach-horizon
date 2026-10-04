"""Freeze only explicit FINAL1/2/6 round15 reports and final numeric production."""
import sys
sys.dont_write_bytecode=True
import argparse,json
from hashlib import sha256
from pathlib import Path
HERE=Path(__file__).resolve().parent; ROUND=HERE.parent; BASE=ROUND.parent
TRUSTED={'agent1_weighted_incidence.md':'8fa44b44dbb2c14fd4a5319840e26a4dc8d113d2db3c6b57dec5569e790bbf5d',
    'previous_artifacts_sha256.json':'d43941b27a4325a841282d389476c9c6fa9af920138b9b0deebe1c484a4ff7f4'}
def digest(p): return sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser()
for n in ('role2-sha','role6-sha','numeric-manifest-sha','role6-receipt-sha'): parser.add_argument('--'+n,required=True)
args=parser.parse_args()
signals={'role1':dict(terminated=True,report='agent1_weighted_incidence.md',report_sha256=TRUSTED['agent1_weighted_incidence.md'])}
for role,n,h in ((2,'agent2_signed_cofactors.md',args.role2_sha),(6,'agent6.md',args.role6_sha)):
    assert len(h)==64 and digest(ROUND/n)==h,n; TRUSTED[n]=h
    signals[f'role{role}']=dict(terminated=True,report=n,report_sha256=h)
TRUSTED['numeric_manifest.json']=args.numeric_manifest_sha
TRUSTED['role6_final_receipt.json']=args.role6_receipt_sha
for n,h in TRUSTED.items(): assert digest(ROUND/n)==h,n
numeric=json.loads((ROUND/'numeric_manifest.json').read_bytes())
assert numeric['status']=='FINAL_FROZEN_NEW_ROUND15_NUMERIC_PARTIAL'
assert numeric['files']==len(numeric['sha256'])
assert numeric['reports_FINAL_sha256']=={n:TRUSTED[n] for n in ('agent1_weighted_incidence.md','agent2_signed_cofactors.md')}
assert numeric['receipt_sha256']==args.role6_receipt_sha
assert numeric['protected_previous_files']==651
for n,h in numeric['sha256'].items(): assert digest(ROUND/n)==h,n
external=json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8')); assert len(external)==2
for n,h in external.items(): assert digest(Path(n))==h,n
files={p.relative_to(ROUND).as_posix():digest(p) for p in sorted(ROUND.rglob('*')) if p.is_file()
    and 'judge' not in p.relative_to(ROUND).parts and '__pycache__' not in p.relative_to(ROUND).parts and p.name!='agent5.md'}
assert not any(n.endswith('.lean') for n in files),'Unexpected new Lean proposal: stop for semantic review'
payload=dict(round=15,status='FINAL_INPUTS_FROZEN',reports=[v['report'] for v in signals.values()],
    final_role_signals=signals,file_count=len(files),sha256=files,external_sha256=external,
    numeric_manifest_sha256=args.numeric_manifest_sha,old_artifacts=651,
    cumulative_auxiliary_modules=15,cumulative_auxiliary_conclusions=208)
dest=HERE/'input_sha256.json'; assert not dest.exists(),'Inputs already frozen'
dest.write_text(json.dumps(payload,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=payload['status'],files=len(files),reports=len(signals),sha256=digest(dest)),indent=2))
