"""Inspect already completed isolated replays; no producers or signs executed."""
import sys
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
from pathlib import Path
from hashlib import sha256
from datetime import datetime
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');R=B/'round18';V=R/'role6';C=B/'.arbor/sessions/parity/.coordinator'
def digest(p):return sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())
assert digest(V/'replay_once.py')=='5b72ca284c70fd2917a5762ef2b834b068e79799c5803a8d68c710cbad92b7df'
rows=[]
for bank in ['typeii','semiprime']:
 r=read(V/(bank+'_replay_receipt.json'));p=read(V/(bank+'_replay_started.json'))
 assert r['bank']==bank and r['attempt']==1 and r['exit_code']==r['comparison_exit_code']==0
 assert r['bytes_identical'] and r['all_fields_identical'] and r['status']=='PASS_UNIQUE_ISOLATED_REPLAY'
 assert r['explicitly_authorized_new_round18_replay'] and not r['old_rounds1_through17_producer_kernel_sign_or_Lean_replayed']
 assert r['command']==p['command'] and p['authorized_distinct_replay']
 assert datetime.fromisoformat(p['started_at_utc'])<=datetime.fromisoformat(p['snapshot_completed_at_utc'])<datetime.fromisoformat(r['finished_at_utc'])
 assert r['source_helper_launcher_registry_sha256_before']==r['source_helper_launcher_registry_sha256_after']==p['source_helper_launcher_registry_sha256']
 for name,h in r['source_helper_launcher_registry_sha256_before'].items():assert digest(R/name)==h
 assert p['snapshots_sha256']==r['snapshots_sha256']
 for name,h in r['snapshots_sha256'].items():assert digest(R/name)==h
 assert digest(R/(bank+'.json'))==digest(R/('isolated_'+bank)/(bank+'.json'))==r['output_sha256']==r['canonical_output_sha256_before']==r['canonical_output_sha256_after']==p['canonical_output_sha256']
 assert (R/(bank+'.json')).read_bytes()==(R/('isolated_'+bank)/(bank+'.json')).read_bytes()
 assert read(R/(bank+'.json'))==read(R/('isolated_'+bank)/(bank+'.json'))
 assert digest(V/(bank+'_canonical_receipt.json'))==r['canonical_receipt_sha256_before']==r['canonical_receipt_sha256_after']==p['canonical_receipt_sha256']
 assert digest(V/(bank+'_replay.log'))==r['log_sha256']
 rows.append(dict(bank=bank,actual_exit_code=0,actual_isolated_replays=1,started_at_utc=r['started_at_utc'],finished_at_utc=r['finished_at_utc'],
  receipt_sha256=digest(V/(bank+'_replay_receipt.json')),started_sha256=digest(V/(bank+'_replay_started.json')),output_sha256=r['output_sha256'],log_sha256=r['log_sha256'],bytes_and_fields_identical=True))
result=dict(status='ROOT_READ_TWO_UNIQUE_ISOLATED18_REPLAYS_PASS',banks=rows,frozen_canonical_sources_helpers_registry_outputs_receipts_unchanged=True,
 root_reran_Lean_producer_sign_or_audit=False,victory=False)
with (C/'messages/round18_replays_root_observation.json').open('x',encoding='utf-8') as h:json.dump(result,h,indent=2);h.write('\n')
p=C/'checkpoint.json';cp=read(p);cp['last_progress']+=' Exactlyoneexplicitlyauthorizedisolatedreplay18perbank actualexit0/0; source/helper/launcher/registry PREEXECsnapshots and canonicalimmutability fullyrootread/hashverified, bytes and fields identical. No additionalproducer/kernel/sign/Lean executedbyroot; numericFINAL6pending.'
for x in cp['in_flight_executors']:
 if x['role']==6:x['status']='two_unique_isolated_replays_actualPASS_drafting_FINAL6_no_more_producers'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/role6/typeii_replay_receipt.json','round18/role6/semiprime_replay_receipt.json','.arbor/sessions/parity/.coordinator/messages/round18_replays_root_observation.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(result))
