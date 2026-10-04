"""Freeze all FINAL round17 author inputs, without executing any author code."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,os,re
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent;ROUND=HERE.parent;BASE=ROUND.parent
EXPECTED={
'agent1_calibrated_typeii.md':'446c2d8fe21c86b05fbaf0e2864e7129da1b964287f31ff4287c0a19251103a9',
'role1/unit_mask_addendum.md':'51735b4ecd379b8b58066d24b952ff779347af5ae8a32ecd4b4ac303b7636cac',
'agent2_capacity_incidence.md':'2c3b2dfadb507925b0fdc92a69b5174353f8f93ba2fc188175dadf05b38ad8d7',
'agent3_formalisation.md':'75386c9030fcb3fba77a3d4888a71fe95ba986ace97a70abacfa7d3e68ec4b03',
'role3/final_receipt.json':'b0e77208bfad5aaf3792de8424922d0945281e2dd77ff74c20efd9b7943031b4',
'agent4_formalisation.md':'59a035188ecab816f3aaf70be0ce4efe4f2d0c4ed5779d9aba597ea429d3fa1c',
'role4/final_receipt.json':'d26e732ec7a4f746689f8ebd43be53118a85f18c689b328e76ea8167846a74ec',
'agent6.md':'629f3ea869c027919970544edf68e9701d8fe3a6d9336a52994d34e1178328af',
'numeric_manifest.json':'c6e1efe0ef1e4c2448bb9d53eb6df1635b29eb9a077723620ce62d4f45a6b1e4',
'role6_final_receipt.json':'6c93e033570fe13e7fe930f947387fc267b9e229b328c03dc171bc96c9e0b8fb',
'agent6_c4.md':'e92c7d210b11743e0079166c29d47195e2ab7a4b36bf110ab0528b991e192bb0',
'role6_c4/manifest.json':'9671e8f8c3ffb32101544103cf57056f6c643aed92d2e86ef4dfadc05b8d6198',
'role6_c4/final_receipt.json':'e6b3d9f8d1d3dc3374b6be67368cd831f43e941f0dd354f3e365635eb8355e91',
'PROBE_BLOCK.md':'cbe1d2a7b02f96ce3743b0b5108c035666be756b4fbe8a83069e4995513e2388',
'previous_artifacts_sha256.json':'1c21af8d00924e126bf541c03f13277fa699c6f8e9d3a9edbbda337b9cead420'}
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1<<20),b''):h.update(block)
 return h.hexdigest()
out=HERE/'input_sha256.json';assert not out.exists(),'Input freeze already exists'
assets={}
for p in sorted(ROUND.rglob('*')):
 if p.is_file() and 'judge' not in p.relative_to(ROUND).parts and '__pycache__' not in p.parts and p.name!='agent5.md':assets[p.relative_to(ROUND).as_posix()]=digest(p)
for name,h in EXPECTED.items():assert assets[name]==h,(name,assets[name],h)
external=json.loads((BASE/'INPUT_HASHES.json').read_text(encoding='utf-8'))
for name,h in external.items():assert digest(Path(name))==h,name
contexts={}
for name in ['round16_feedback.md','round17_primary_source_context.md']:
 p=BASE/'.arbor/sessions/parity/.coordinator/messages'/name;contexts[str(p)]=digest(p)
lean=Path(r'C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe')
assert digest(lean)=='8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08'
result={'status':'FROZEN_ALL_FINAL_ROUND17_AUTHOR_INPUTS','timestamp_utc':datetime.now(timezone.utc).isoformat(),
 'sha256':assets,'files':len(assets),'final_role_signals':EXPECTED,'external_originals_sha256':external,
 'fixed_contexts_sha256':contexts,'lean_executable':str(lean),'lean_sha256':digest(lean),
 'initial_numeric_bindings':33,'distinct_C4_bindings':15,'protected_previous':799,
 'all_FINAL_notifications_received':True,'producer_or_Lean_executed':False,'victory':False}
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
print(json.dumps({'status':result['status'],'files':len(assets),'input_manifest_sha256':digest(out)}))
