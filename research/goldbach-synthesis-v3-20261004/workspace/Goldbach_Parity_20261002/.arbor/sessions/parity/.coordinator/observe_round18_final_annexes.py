"""Coordinator hashes frozen CRT/content FINALs; no audit or mathematical execution."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002');R=B/'round18';C=B/'.arbor/sessions/parity/.coordinator'
def h(p):return sha256(Path(p).read_bytes()).hexdigest()
def load(p):return json.loads(Path(p).read_text(encoding='utf-8-sig'))
def verify(mp):
 for name,expected in mp.items():assert h(B/name)==expected,name
content=load(R/'role5_content/final_receipt.json');cm=load(R/'role5_content/manifest.json')
assert h(R/'agent5_content.md')==content['report_sha256']=='31ac4754529f0faf0418f3a6ca0083413180f5962f9b06193bdde9dc19cfdade'
assert h(R/'role5_content/manifest.json')==content['manifest_sha256']=='d989cac73826ed0fd17924ba781b88f77c15c7e0288380b253e173c3475fa0ab'
assert h(R/'role5_content/final_receipt.json')=='37b1670fd92b2248ae78b19244c79ce3b17abd821f79ce76de6c6d93a884bc72'
assert len(cm['bindings'])==content['bound_inputs']==cm['bound_input_count']==37
for name,item in cm['bindings'].items():assert h(B/name)==item['sha256'] and (B/name).stat().st_size==item['bytes']
crt=load(R/'role6_crt/final_receipt.json');m=load(R/'role6_crt/manifest.json');closure=load(R/'role6_crt/closure_receipt.json')
assert h(R/'agent6_crt.md')==crt['report_sha256']=='a29cfc376d2daa28c1681a2a46fb0562a5982f933ad502723a9575b2e895200a'
assert h(R/'role6_crt/manifest.json')==crt['manifest_sha256']=='66b2bbf6884cb3fc27afcab847259f068a91f40378354f31c5d7874d2e9101b4'
assert h(R/'role6_crt/final_receipt.json')=='54bcbf41e6a7e1c7701db1aa1605c378c4085f07edf10f13a093a6a51460e8ed'
assert h(R/'role6_crt/closure_receipt.json')=='234d4ee75aacbb03d0a060322401aa0b49eb9ed2eafa2b357a5b71bc7d36b8c8'
assert len(m['owned_artifacts_sha256'])==m['owned_bindings_count']==35
assert len(m['read_only_inputs_sha256'])==m['readonly_bindings_count']==11
assert len(crt['bindings_sha256'])==crt['bindings_count']==47
for mp in [m['owned_artifacts_sha256'],m['read_only_inputs_sha256'],crt['bindings_sha256'],closure['bindings_sha256']]:verify(mp)
assert crt['actual_numeric_attempts']==1 and crt['actual_numeric_failures']==crt['isolated_replays']==0
assert not crt['replay_authorized'] and not crt['victory'] and not content['victory']
assert closure['metadata_exit_code']==0 and closure['numeric_processes_rerun_by_closure']==0
actual=load(R/'role6_crt/finalize_attempt01_receipt.json')
assert actual['exit_code']==0 and actual['actual_metadata_subprocess_returned']
assert actual['source_sha256']==actual['source_after_sha256']==actual['source_snapshot_sha256']==h(R/'role6_crt/finalize_metadata.py')==h(R/'role6_crt/finalize_attempt01_source.py.txt')
assert actual['launcher_sha256']==actual['launcher_after_sha256']==actual['launcher_snapshot_sha256']==h(R/'role6_crt/close_once.py')==h(R/'role6_crt/finalize_attempt01_launcher.py.txt')
assert actual['started_sha256']==h(R/'role6_crt/finalize_attempt01_started.json') and actual['log_sha256']==h(R/'role6_crt/finalize_attempt01.log')
obs=dict(status='ROOT_INSPECTED_ALL_DISTINCT_FINAL18_ANNEXES_FROZEN',utc=datetime.now(timezone.utc).isoformat(),content_input_bindings=37,CRT_owned_bindings=35,CRT_readonly_bindings=11,CRT_final_bindings=47,CRT_canonical_invocations=1,CRT_replays=0,CRT_metadata_actual_exit=0,content_verdict='AUXILIARY_CONDITIONAL_NO_WIN',root_reran_finalizer_or_audit_or_producer_or_Lean=False,independent_judge_authorized=False,victory=False)
dest=C/'messages/round18_final_annexes_root_observation.json'
with dest.open('x',encoding='utf-8') as f:json.dump(obs,f,indent=2);f.write('\n')
cpPath=C/'checkpoint.json';cp=load(cpPath)
cp['phase']='ROUND18_ALL_FINALS_FROZEN_JUDGE_FINAL_PREPARATION'
cp['in_flight_executors']=[dict(role=5,agent='/root/round18_independent_judge',status='final_preparation_only_audit_Lean_not_yet_authorized')]
cp['last_progress']+=' FINAL6CRT and independentcontentFINAL fullrootread with allmetadatafinalizer/launcher/log/receipts; rootverifies35owned+11readonly/47finalCRTbindings and37contentinputs, actualCRTclosingexit0, no rerun. Content finds no induced theoremglitch but real applicationgaps R6/sourceguards/SSroughbridge/prime-log/Mertens/totient/CRT1/allparams/onsetgap/Srest/T_A/wholeGamma/ledger. All FINAL18 now frozen. Judgefinalpreparation awaits separateexplicitauthorization; official22/337 unchanged, Winfalse.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round18/agent6_crt.md','round18/role6_crt/final_receipt.json','round18/role6_crt/closure_receipt.json','round18/agent5_content.md','round18/role5_content/final_receipt.json',str(dest.relative_to(B)).replace('\\','/')]))
cpPath.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(status=obs['status'],CRT_bindings=47,content_inputs=37,observation_sha256=h(dest))))
