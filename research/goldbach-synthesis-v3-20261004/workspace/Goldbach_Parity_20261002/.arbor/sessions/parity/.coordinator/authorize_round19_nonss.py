"""Authorize the fully read NEW numeric19 source; metadata only, no producer."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json
from datetime import datetime, timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
R=B/'round19';C=B/'.arbor/sessions/parity/.coordinator'
def read(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
expected={
 'nonss_checks.py':'a68438eed436be3bd88d6e7e19bd3375622f9298fd18f27a796e0eed7cae3d7b',
 'role6_nonss/arithmetic.py':'cd6b82ca09ae15289887dc9381a858d338d3d2047a04887a144de49e19665cc2',
 'role6_nonss/bank.py':'11865a7f9fe6147c9fa07da2131649cffadaac73d4fc0335d562af22ce5ab4e9',
 'role6_nonss/run_nonss_once.py':'a2366f9777d756380ef08c192b308ac43433b66e3f335d0d7f83246effa8d5a0',
 'role6_nonss/preparation.json':'e8f7a40704d600f91f92e417cf2092a9b72708fbbeb6156333f9f33dd8ff59a3'}
out=C/'messages/round19_nonss_authorization.json'
assert not out.exists()
assert not (R/'role6_nonss/canonical_attempt01').exists() and not (R/'nonss.json').exists()
for rel,h in expected.items():assert digest(R/rel)==h,rel
prep=read(R/'role6_nonss/preparation.json')
assert len(prep['bindings'])==12 and prep['mathematical_producer_invocations']==0
for name,spec in prep['bindings'].items():
    p=Path(spec['path']);data=p.read_bytes()
    assert p.is_relative_to(B)
    assert sha256(data).hexdigest()==spec['sha256'] and len(data)==spec['bytes'],name
assert read(C/'messages/round19_role2_selection.json')['node']=='14.4'
assert read(C/'messages/round19_conservation_root_observation.json')['status']=='ROOT_VERIFIED_ACTUAL_UNIQUE_CONSERVATION19'
token='ROOT19_NONSS_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01'
command=[sys.executable,'-B','-X','utf8',str(R/'role6_nonss/run_nonss_once.py'),
 '--root-authorization',token,'--source-sha256',expected['nonss_checks.py'],
 '--launcher-sha256',expected['role6_nonss/run_nonss_once.py'],
 '--preparation-sha256',expected['role6_nonss/preparation.json']]
receipt=dict(status='ROOT19_NONSS_UNIQUE_NEW_CANONICAL_AUTHORIZED_AFTER_FULL_READ',
 authorized_utc=datetime.now(timezone.utc).isoformat(),token=token,node='14.4',
 source_launcher_preparation_sha256=expected,bindings12_verified=True,
 full_source_read_chunks=['c2f10f','cc909f arithmetic full','eb44cb bank full final'],
 new_command_authorized=command,canonical_attempts_authorized=1,replay_authorized=False,
 mathematical_producer_executed_by_root=False,new_producer_start_observed=False,
 no_old_producer_preflight_Lean_PDF_execution=True,compiler_gate_still_closed=True,victory=False,
 actual_review=['all1001 integers/allperqSFunitcores beforeprime masks',
 'literal oldA/R/S/SS matched by source read only',
 'e1/e3 exceptions, universalC/F1 onlye>p0 andqprime',
 'allrank/repeatedfactors/signedCRT/3strata/front+1 and both inverses',
 'theta/raw/properpowers literal, unique physicaltarget/m1, mu-zero nofakeW',
 'H8 completeuncut2048 inclprime-squared diagonal',
 '128bitoutward rational atanh48/geometric tail, nofloats/assumedsigns',
 'imports onlynewcapturedhelpers, exclusive13captures andreceipt onfail',
 'source1e24/local1e40 notfiniteonsets, no analyticalpayment'])
out.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp['phase']='ROUND19_NONSS_NEW_CANONICAL_SOURCE_AUTHORIZED_NOT_YET_START_OBSERVED'
cp['last_progress']+=' NEWnonSS source/bank/arithmetic/launcher/preparation fullyread and12bindingsSHAverified; distinctunique canonical14.4 authorization saved. Actualstart notyetobserved; Lean gatesclosed, sourceonsets/longcosts/fullledger unpaid, noWin.'
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['.arbor/sessions/parity/.coordinator/messages/round19_nonss_authorization.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print('DistinctROOT19_NONSS gate saved; uniqueNEWproducer authorized, not executed byroot; noLean/noWin')
