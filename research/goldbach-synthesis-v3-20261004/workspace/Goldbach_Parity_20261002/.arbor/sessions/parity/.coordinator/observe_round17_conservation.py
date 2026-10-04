"""Independent controller conservation audit; do not invoke preflight, producers or Lean."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import os,re,json
BASE=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
RND=BASE/'round17';COORD=BASE/'.arbor/sessions/parity/.coordinator'
def read(p):return json.loads(p.read_bytes())
def sha(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
expected={'previous_artifacts_sha256.json':'1c21af8d00924e126bf541c03f13277fa699c6f8e9d3a9edbbda337b9cead420',
          'conservation.py':'95dd8a69f704c2f96fee6cea9a1e388513a29dcb3e097b57c9a612a87647db37',
          'conservation.json':'b3994fd8eb7ac9164eb01dccec1b5ad9556ab963811882b83c7c75cd35a91412',
          'role6/conservation_final_receipt.json':'b6c71dccfadaf14a452b274e43d1a5788850454d0fb47be1ff097a83e35207f0'}
for n,h in expected.items():assert sha(RND/n)==h,n
f=read(RND/'role6/conservation_final_receipt.json')
assert f['attempts']==1 and f['exit_code']==0 and f['total_protected']==799
assert f['old_producer_or_compiler_executed'] is False and f['new_numeric_contract_executed_by_this_preflight'] is False
for n,h in f['sha256'].items():assert sha(RND/n)==h,n
assert (RND/'role6/conservation_attempt01.log').read_bytes()==(RND/'conservation.json').read_bytes()
assert (RND/'role6/conservation_attempt01_source.txt').read_bytes()==(RND/'conservation.py').read_bytes()
old=read(BASE/'round16/previous_artifacts_sha256.json')['sha256']
c=read(BASE/'round16/controller_manifest.json')
assert len(old)==701 and len(c['bindings_sha256'])==97
ch=sha(BASE/'round16/controller_manifest.json')
assert ch=='10d9f68fc649d965aa5eecac96fecf5fd20f705527d42f52b855662acec02332'
union=dict(old);union.update({'round16/'+n:h for n,h in c['bindings_sha256'].items()})
union['round16/controller_manifest.json']=ch
registry=read(RND/'previous_artifacts_sha256.json')
assert registry['file_count']==len(registry['sha256'])==len(union)==799 and registry['sha256']==union
actual={}
skip={'.git','.lake','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'}
for top,dirs,files in os.walk(BASE,followlinks=False):
    dirs[:]=[d for d in dirs if d not in skip and not(re.fullmatch(r'round\d+',d) and int(d[5:])>=17)]
    for n in files:
        p=Path(top)/n
        if p==BASE/'REPORT.md':continue
        actual[p.relative_to(BASE).as_posix()]=sha(p)
assert actual==union,'Protected inventory mismatch'
originals=read(BASE/'INPUT_HASHES.json')
for n,h in originals.items():assert sha(Path(n))==h,n
observation=dict(recorded_utc=datetime.now(timezone.utc).isoformat(),status='ROOT_INDEPENDENT_799_CONSERVATION_VERIFIED',
    files=799,previous_files=701,round16_files=98,controller_bindings=97,registry_sha256=expected['previous_artifacts_sha256.json'],
    controller16_sha256=ch,bindings_sha256=expected,original_sources_sha256=originals,
    full_source_and_captured_log_read=True,exact_inventory_and_hash_union_verified=True,
    preflight_scope_preserved=True,no_preflight_or_math_producer_or_compiler_reexecuted=True,
    new_candidate_selection_pending=True,new_numeric_contract_launched=False,victory=False)
(COORD/'messages/round17_root_conservation.json').write_text(json.dumps(observation,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=COORD/'checkpoint.json';checkpoint=read(p)
checkpoint.update(current_protected_artifacts=799,current_protected_registry='round17/previous_artifacts_sha256.json',
    current_protected_registry_sha256=expected['previous_artifacts_sha256.json'],next_protected_registry_pending=None)
checkpoint['last_progress']+=' Root17 read conservation source/captured log/final receipt and independently verified exact old701+final16count98 union799, all actual inventory/hashes and original sources. No preflight/math producer/compiler rerun. Two mathematical ideations remain active; no17 bank or Lean selected.'
checkpoint['previous_goal_turn_evidence']+=['round17/conservation.py','round17/conservation.json','round17/previous_artifacts_sha256.json','round17/role6/conservation_final_receipt.json','.arbor/sessions/parity/.coordinator/messages/round17_root_conservation.json']
p.write_text(json.dumps(checkpoint,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=observation['status'],protected=799,controller_bindings=97,originals=2,no_reexecution=True,victory=False)))
