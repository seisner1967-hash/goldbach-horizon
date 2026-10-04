"""Metadata-only gate for the unique NEW rank bank; never runs its sources."""
import ast,json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round19'; C=B/'.arbor/sessions/parity/.coordinator'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
expected={
 'allrang_checks.py':'0cbaa0391cd2b9e82cae99b5f6a88c755bde2da946bcebb988874dfd9acd33d9',
 'role6_rank/strict_rank.py':'c651e6e20e7df683d95ef81158cb46f6a0ee2f55da21d9d342d6c6cfe9b35122',
 'role6_rank/rank_bank.py':'85bbfa160594678ae4f21f66dd910d2062a589bdf35c4e14b623963fc0ae5008',
 'role6_rank/run_rank_once.py':'503b22b09069147c9127ca574b6d75bfdb4dfe83698f4722aaa391daa1dc4254',
 'role6_rank/test_contract.json':'d86271c581567bf603ea76b6a24e0b74b1b753096c72e42b07d4f8f3d9aca1b1',
 'role6_rank/preparation.json':'082322fab71923e1ed036c1d480f1700106a62ca7eb2783c41abd7d024be27a0'
}
for rel,digest in expected.items():
    p=R/rel
    assert sha(p)==digest,rel
    if p.suffix=='.py': ast.parse(p.read_text(encoding='utf-8'),filename=str(p))
prep=json.loads((R/'role6_rank/preparation.json').read_text(encoding='utf-8'))
assert prep['node']=='13.11' and prep['mathematical_producer_invocations']==0
assert prep['Lean_invocations']==0 and prep['gate_authorized'] is False
assert len(prep['bindings'])==12
for name,binding in prep['bindings'].items():
    p=Path(binding['path'])
    assert p.is_relative_to(B) and sha(p)==binding['sha256'],name
    assert p.stat().st_size==binding['bytes'],name
assert not (R/'allrang.json').exists()
assert not (R/'role6_rank/canonical_attempt01').exists()
python=Path(r'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe')
assert sha(python)=='4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c'
token='ROOT19_RANK_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01'
command=[str(python),'-B','-X','utf8',str(R/'role6_rank/run_rank_once.py'),
 '--root-authorization',token,'--source-sha256',expected['allrang_checks.py'],
 '--launcher-sha256',expected['role6_rank/run_rank_once.py'],
 '--preparation-sha256',expected['role6_rank/preparation.json']]
gate={
 'status':'ROOT19_RANK_DISTINCT_UNIQUE_CANONICAL_AUTHORIZATION_AFTER_FULL_READ',
 'authorized_at_utc':datetime.now(timezone.utc).isoformat(),'round':19,'node':'13.11',
 'authorization':token,'exact_authorized_command':command,
 'fully_read_current_owned_sources_sha256':expected,'prepared_bindings':prep['bindings'],
 'syntax_only_AST_parse_without_execution':True,
 'numeric_or_Lean_execution_by_root':0,'actual_start_not_yet_observed':True,
 'scope':'Unique first NEW canonical01 only; capture12inputs+preparation before subprocess. Preserve all failed artifacts/logs/receipts; no automatic replay. No old bank/kernel/W/D/preflight/PDF/Lean invocation. Lean3 gate waits actual PASS root review.',
 'complete_domain':'all12000000 j positions and ALL eligible c<r unitN cr<=3163, A0 retained',
 'prices_and_PP_and_fronts_retained':True,'source_onset_or_BV_applied':False,
 'metadata_reader_transient_incident':'One exec process creation rejected deny-read ACL setup in batch before launcher read; independent readonly retryf75a20 succeeded. No producer executed and no unresolved blocker.',
 'official_Judge_counts_modified':False,'victory':False
}
p=C/'messages/round19_rank_authorization.json'
with p.open('x',encoding='utf-8') as f: f.write(json.dumps(gate,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'status':gate['status'],'authorization':token,'authorized_command':command,
 'gate_sha256':sha(p),'checked_preparation_bindings':12,'victory':False}))
