"""Root hash/inventory observation of an existing preflight; no producer run."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,os,re
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';R=B/'round18'
def h(p):
    d=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):d.update(block)
    return d.hexdigest()
def read(p):return json.loads(p.read_bytes())
rec=read(R/'role6/conservation_attempt01_receipt.json');out=read(R/'conservation.json')
assert rec['attempt']==1 and rec['exit_code']==0 and rec['state']=='FINISHED'
assert h(R/'role6/conservation_attempt01_receipt.json')=='a043bbd744d0757919d80deed22b1793f79f2c43bb7343084509f9b06c37d2be'
assert h(R/'conservation.py')==h(Path(rec['snapshot']))==rec['source_sha256_before_execution']==rec['source_sha256_after_execution']==rec['snapshot_sha256']=='b3bb16ef74a74cf25a5f2bc5ceaf6bd248ec362818ec324ac9f5922ba076dcf4'
assert h(R/'role6/run_conservation_once.py')==rec['launcher_sha256']=='e78923afd2beb6173d6b494dccef8f2503f028ef0720eaa0cf39ed5169e8c838'
assert h(Path(rec['log']))==h(R/'conservation.json')==rec['log_sha256']==rec['conservation_sha256']=='480f1693130bcbf8c0e61500d01bb91ba1cd66eafa73640b1db93f687f0b7509'
started=read(R/'role6/conservation_attempt01_started.json')
assert h(R/'role6/conservation_attempt01_started.json')=='86e77232357fc54048881ef27546b8b432147677c92d411190e85175bd93ead5'
assert not started['snapshot_pending'] and started['source_sha256']==rec['source_sha256_before_execution']
assert started['command']==rec['command'] and started['started_at_utc']==rec['started_at_utc']
assert len(list((R/'role6').glob('conservation_attempt*_receipt.json')))==1
registry=read(R/'previous_artifacts_sha256.json');old=read(B/'round17/previous_artifacts_sha256.json')['sha256'];m=read(B/'round17/controller_manifest.json')
added={'round17/'+name:value for name,value in m['bindings_sha256'].items()};added['round17/controller_manifest.json']=h(B/'round17/controller_manifest.json')
assert len(old)==799 and len(added)==198 and not set(old)&set(added)
assert registry['sha256']==dict(old,**added) and registry['file_count']==len(registry['sha256'])==997
actual={}
for root,dirs,files in os.walk(B):
    dirs[:]=[d for d in dirs if d not in {'.git','.lake','.arbor','__pycache__','.pytest_cache','.mypy_cache','.ruff_cache'} and not (re.fullmatch(r'round\d+',d) and int(d[5:])>=18)]
    for name in files:
        p=Path(root)/name
        if p!=B/'REPORT.md':actual[p.relative_to(B).as_posix()]=h(p)
assert actual==registry['sha256']
assert out['status']=='PRESERVED' and out['files']==997 and not out['changed'] and not out['added'] and not out['removed']
for path,value in read(B/'INPUT_HASHES.json').items():assert h(Path(path))==value==out['original_sources'][path]['actual_sha256']
obs=dict(status='ROOT_VERIFIED_EXISTING_UNIQUE_PREFLIGHT18',actual_preflight_attempts=1,actual_preflight_exit_code=0,exact_inventory997=True,
         union799plus198_exact=True,originals_preserved=True,source_snapshot_log_receipt_started_bindings_verified=True,
         root_reran_preflight_or_math_producer=False,new_node_or_mathematical_bank_selected=False,victory=False)
(C/'messages/round18_root_conservation.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp['phase']='ROUND18_UNIQUE_PREFLIGHT997_PASS_QUANTITATIVE_IDEATION_ACTIVE'
cp['in_flight_executors']=['round13_formal3_switch: role1 actual ideation active; identified one chi13 mode does not control whole TypeII/Gamma theta, new estimate under research',
                         'round13_bilateral_ideation: role2 runtime running, nonrough A/S quantitative ideation dispatched',
                         'round18_numeric_conservation: actual unique997 preflight exit0 and all sources/originals preserved; waits exact new candidate selection']
cp['last_progress']+=' Role1 actual research confirms remaining whole-TypeII/price obligation and II_prime zero on v17/19 product slice; not a fresh hypothesis or selectednode. Role6 actual unique18preflight exit0 at21:02:01UTC captures snapshot/source/launcher/log/result/receipt/started marker, exact997/799+198/originals. Root fully reads source and actuallog/receipts, independently hashes exact997 union/inventory and originals, verifies allpreexecutionbindings without rerunning preflight/math. Twoideators remain active; no18node/bank/Lean selected or launched. No externalblocker or Win.'
cp['previous_goal_turn_evidence']+=['round18/conservation.py','round18/conservation.json','round18/role6/conservation_attempt01_receipt.json',
    '.arbor/sessions/parity/.coordinator/messages/round18_root_conservation.json']
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
with (B/'REPORT.md').open('a',encoding='utf-8') as f:
    f.write('\nLe préflight18 a été réellement exécuté une seule fois exit0 à21:02:01UTC : inventaire997=799+198 etoriginaux intacts. Root lit source/log/receipts et vérifie les empreintes/inventaire sans rerun. Le rôle1 confirme que le modechi13 ne contrôle pas toutTypeII/Gammaθ etcherche une estimation indépendante avec prix réels. Les deuxidéations sontactives ; rôle6 attendla sélection. Aucun node/bancmathématique/Lean18 sélectionné.\n')
print(json.dumps(obs))
