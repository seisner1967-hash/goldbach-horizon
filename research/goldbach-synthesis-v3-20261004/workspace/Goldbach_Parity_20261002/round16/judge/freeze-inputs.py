"""Freeze explicit FINAL1/2/3/4/6 inputs before the single independent audit."""
import sys
sys.dont_write_bytecode=True
import argparse,json
from pathlib import Path
from hashlib import sha256
HERE=Path(__file__).resolve().parent;ROUND=HERE.parent;BASE=ROUND.parent
def digest(p):return sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('--role3-sha',required=True);args=parser.parse_args()
reports={1:('agent1_bilinear_covariance.md','f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754'),
 2:('agent2_or_incidence.md','f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b'),
 3:('agent3_formalisation.md',args.role3_sha),
 4:('agent4_formalisation.md','b12adfa9f03ed0af0735278946ebbf09f9bf41e3a6c4d42cc8912ddedb0097b7'),
 6:('agent6.md','8b540e65d2f8b451beebb9905f6a7ad43d9f2b1616256c2dc15199a5e8b456cc')}
for role,(n,h) in reports.items():assert len(h)==64 and digest(ROUND/n)==h,(role,n)
assert digest(ROUND/'numeric_manifest.json')=='29e8a7a9aeb34504dbdef9d88d7b46ce49b46fd83f8ac384b6db4346033373ce'
assert digest(ROUND/'role6_final_receipt.json')=='5d3a0018e74e6b5e64aa8ee73fe856d176bcb45648a6bf9d2ba40a89d67ec208'
for role in (3,4):
    receipt=json.loads((ROUND/f'role{role}/final_receipt.json').read_bytes())
    assert receipt['victory'] is False and receipt['report_sha256']==reports[role][1]
numeric=json.loads((ROUND/'numeric_manifest.json').read_bytes())
assert numeric['status']=='FINAL_FROZEN_NEW_ROUND16_NUMERIC_PARTIAL' and numeric['files']==len(numeric['sha256'])==30
for n,h in numeric['sha256'].items():assert digest(ROUND/n)==h,n
external=json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8'));assert len(external)==2
for n,h in external.items():assert digest(Path(n))==h,n
files={p.relative_to(ROUND).as_posix():digest(p) for p in sorted(ROUND.rglob('*')) if p.is_file()
    and 'judge' not in p.relative_to(ROUND).parts and '__pycache__' not in p.relative_to(ROUND).parts and p.name!='agent5.md'}
payload=dict(round=16,status='FINAL_INPUTS_FROZEN',reports=[n for n,h in reports.values()],
    final_role_signals={f'role{k}':dict(terminated=True,report=n,report_sha256=h) for k,(n,h) in reports.items()},
    file_count=len(files),sha256=files,external_sha256=external,
    numeric_manifest_sha256=digest(ROUND/'numeric_manifest.json'),old_artifacts=701,
    cumulative_auxiliary_modules_before=15,cumulative_auxiliary_conclusions_before=208)
dest=HERE/'input_sha256.json';assert not dest.exists(),'Inputs already frozen'
dest.write_text(json.dumps(payload,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=payload['status'],files=len(files),reports=5,sha256=digest(dest)),indent=2))
