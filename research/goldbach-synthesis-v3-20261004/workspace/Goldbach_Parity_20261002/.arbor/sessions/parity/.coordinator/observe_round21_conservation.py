"""Observe actor6 actual receipts/snapshots/bytes; do not execute the preflight."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); R=B/'round21'; O=R/'role6'; C=B/'.arbor/sessions/parity/.coordinator'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''): h.update(b)
    return h.hexdigest()
receipt=O/'conservation_attempt01_receipt.json'; r=read(receipt)
assert sha(receipt)=='c23ac6570207f0e27131375d97867363c12d5df58cfb19b87f158ac326a492fa'
assert r['exit_code']==0 and r['credited_pass'] and r['post_unchanged'] and r['launch_error'] is None and r['result_parse_error'] is None
assert r['started_at_utc']=='2026-10-03T05:18:32.248223+00:00' and r['finished_at_utc']=='2026-10-03T05:18:40.795646+00:00'
assert r['new_preflight_subprocess_invocations']==1 and r['Lean_executions']==r['old_preflights_executed']==r['protected_files_written']==0
assert not r['mathematical_execution'] and not r['victory'] and not r['old_producer_or_Lean_or_PDF_execution']
assert sha(Path(r['result']))==r['result_sha256']=='51211ade1ad6cc490e724637c1e0d4602a3f184e46dd971eb6c282892e63208f'
assert sha(Path(r['log']))==r['log_sha256']=='9fef6095f1e90439c9bd16ae1bcc97ef642b304305d9b0c21d328ffd6c00be7a'
assert sha(Path(r['post_integrity']))==r['post_integrity_sha256']=='e8f228a9e014ae3f72a1d49da33e5fc5be2691f63d10d80e944a4274bb04bcf6'
assert sha(Path(r['authorization']))==r['authorization_sha256']=='0ea14a4f47058f38817fd975a2e5b2d7a1b95d2e0940b66ae57c90e63c6189f7'
start=O/'conservation_attempt01_started.json'; assert sha(start)==r['started_receipt_sha256']
for key,value in read(start).items(): assert r[key]==value,key
assert len(r['captures_preexec'])==8
for row in r['captures_preexec'].values():
    assert sha(Path(row['snapshot']))==sha(Path(row['original']))==row['sha256']
    assert Path(row['snapshot']).stat().st_size==row['bytes']
assert r['subprocess_command']==[r['runtime']['path'],'-B','-X','utf8',r['captures_preexec']['source']['snapshot']]
assert r['cwd']==str(R) and r['environment_changes']=={'PYTHONDONTWRITEBYTECODE':'1','PYTHONUTF8':'1'}
assert sha(Path(r['runtime_preexec_receipt']))==r['runtime_preexec_receipt_sha256']
assert sha(Path(r['originals_preexec_receipt']))==r['originals_preexec_receipt_sha256']
post=read(Path(r['post_integrity'])); assert post['checked_path_count']==len(post['observed_sha256'])==23
assert post['unchanged'] and post['changed']==[] and post['metadata_only']
for path,d in post['observed_sha256'].items(): assert sha(Path(path))==d,path
result=read(Path(r['result'])); registry=read(R/'previous_artifacts_sha256.json')['sha256']
assert result['status']==r['result_status']=='PASS_EXACT_CONSERVATION'
assert result['unchanged_between_stages'] and result['expected_file_count']==3028
assert result['before']==result['after']
for side in ('before','after'):
    row=result[side]
    assert row['passed'] and row['actual_file_count']==row['checked_sha256_count']==3028
    assert row['missing']==row['extra']==row['changed']==[]
    assert set(row['exact_inventory_names'])==set(registry) and row['observed_sha256']==registry
    assert row['original_hash_map_equal']
    for path,entry in row['originals'].items(): assert sha(Path(path))==entry['actual']==entry['expected']
# Byte verification of stored bindings only, not a second inventory/preflight producer or mathematical execution.
for path,d in registry.items(): assert sha(B/path)==d,path
obs={'status':'ROOT_VERIFIED_ACTUAL_UNIQUE_CONSERVATION21_PASS',
 'observed_utc':datetime.now(timezone.utc).isoformat(),'actual_start_utc':r['started_at_utc'],'actual_finish_utc':r['finished_at_utc'],
 'actual_child_invocations':1,'actual_child_exit_code':0,'credited_pass':True,'protected_byte_bindings_verified':3028,
 'PREEXEC_capture_count':8,'post_path_count':23,'result_sha256':r['result_sha256'],'receipt_sha256':sha(receipt),
 'started_sha256':sha(start),'log_sha256':r['log_sha256'],'post_integrity_sha256':r['post_integrity_sha256'],
 'root_full_receipt_read_chunk':'1da25f','root_full_log_read_chunk':'059df3',
 'large_result_dictionaries':'Parsed exact-key/field consistency and all bytes verified, not claimed FULL textual display.',
 'metadata_only':True,'root_preflight_producer_compiler_math_log_or_sign_invocations':0,'new_math_Lean_authorized':False,'victory':False}
(C/'messages/round21_conservation_root_observation.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json'; cp=read(p); cp['phase']='ROUND21_UNIQUE_CONSERVATION_PASS_IDEATION_FINALS_PENDING'
cp['last_progress']+=' Actualuniqueconservation21 START05:18:32..05:18:40UTCexit0/creditedtrue;3028bytes/nochanges/2originals/8PREEXEC/23postpathsrootverified;FULLreceipt1da25f/log059df3;0math/Lean/oldreplay,noWin. IdeationFINALspending.'
cp['previous_goal_turn_evidence']+=['round21/conservation.json','round21/role6/conservation_attempt01_receipt.json','.arbor/sessions/parity/.coordinator/messages/round21_conservation_root_observation.json']
p.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
