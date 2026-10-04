"""Coordinator observations only; no arithmetic producer, replay or Lean invocation."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import hashlib,json

root=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
coord=root/'.arbor/sessions/parity/.coordinator'
receipt_path=coord/'messages/round16_root_capacity_margin_observation.json'
assert not receipt_path.exists(), 'Observation already recorded; inspect it.'
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as stream:
        for chunk in iter(lambda:stream.read(1024*1024),b''):
            h.update(chunk)
    return h.hexdigest()
expected={
 'round16/capacity_checks.py':'abedd2b6494ebb684fcaeef2ca0d869003f2ee17271dbde1cd70f52820367128',
 'round16/capacity.json':'7da550e67c38774e580dd6300b1c78a9d19cb4f49e3063483a6727d7ecd2a166',
 'round16/isolated_capacity/capacity.json':'7da550e67c38774e580dd6300b1c78a9d19cb4f49e3063483a6727d7ecd2a166',
 'round16/agent4_formalisation.md':'b12adfa9f03ed0af0735278946ebbf09f9bf41e3a6c4d42cc8912ddedb0097b7',
 'round16/role4/final_receipt.json':'7272776cc0725acd02438bcf99d04746762c5e9164c56117f430a5f5c7d5caa0',
}
for rel,h in expected.items():
    assert digest(root/rel)==h,rel
replay=json.loads((root/'round16/role6/capacity_replay_receipt.json').read_text(encoding='utf-8'))
assert replay['exit_code']==0 and replay['bytes_identical'] and replay['all_fields_identical']
assert replay['output_sha256']==expected['round16/capacity.json']
summary=json.loads((root/'round16/role6/capacity_attempt01.log').read_text(encoding='utf-8').strip().splitlines()[-1])
assert summary['q_count']==18 and summary['core_count']==34 and summary['candidate_vertices']==612
assert summary['computed_profiles']==128 and summary['proper_powers']==0
assert summary['principal_deficit_signs']=={'lower':'POSITIVE','upper':'POSITIVE'}
assert summary['actual_deficit_R13_sign']==summary['actual_entire_sign']=='POSITIVE'
assert not summary['victory']
r4=json.loads((root/'round16/role4/final_receipt.json').read_text(encoding='utf-8-sig'))
assert r4['exit_code']==0 and r4['theorem_count']==9 and r4['definition_count']==0
assert r4['actual_Lean_failures']==r4['source_banned_token_count']==0
for entry in r4['files']:
    p=Path(entry['path'])
    assert p.is_relative_to(root/'round16/role4')
    assert p.stat().st_size==entry['bytes'] and digest(p)==entry['sha256']
    expected[p.relative_to(root).as_posix()]=entry['sha256']
for rel in ['round16/role6/capacity_replay_receipt.json','round16/role6/capacity_attempt01.log','round16/role6/capacity_isolated_replay.log']:
    expected[rel]=digest(root/rel)
receipt={
 'status':'ROOT_OBSERVED_NEW_CAPACITY_BANK_AND_FROZEN_HARMONIC_MODULE_NO_REEXECUTION',
 'bindings_sha256':expected,
 'capacity_log_summary':summary,
 'new_harmonic_theorems_producer':9,
 'new_harmonic_source_read_in_full':True,
 'new_capacity_source_read_in_full':True,
 'capacity_large_gate_not_dumped_or_reexecuted':True,
 'producer_invoked_by_root':False,'Lean_invoked_by_root':False,
 'Judge16_audit_pending':True,'full_anchor_A7_Lean_pending':True,
 'coordination_incident':'Old Judge followup and fresh Judge spawn returned agent thread limit while a completed ideator appears pending_init. Judge dispatch awaits release of another slot; no audit or proof was started by those failed calls.',
 'victory':False,
}
receipt_path.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
cp_path=coord/'checkpoint.json'
cp=json.loads(cp_path.read_text(encoding='utf-8'))
cp['phase']='ROUND16_REAL_ANCHOR_PROOF_IN_PROGRESS_AND_JUDGE_PREPARATION_PENDING'
cp['in_flight_executors']=[
 'round16_formal3_anchor:role3 final real-product A7 proof after genuine technical compile attempts',
 'round13_formal3_switch:role6 frozen final reports/manifests after two successful new banks',
 'round13_bilateral_ideation:completed FINAL2; spurious pending_init after failed old-Judge followup, no new work assigned'
]
cp['coordination_incident']=receipt['coordination_incident']
cp['last_progress']+=' Root16 FULLread frozen FINAL4/source/compilehelper/log/finalreceipt, oneproducerexit0 nineharmonic/logtheorems standardaxioms sourcee1dbd4... independentlyhashbound noLeanroot. Secondnewbank canonicalPASS1+uniqueisolatedidentical7da550... FULLcapacitysource/readlogs/receiptroot;18q34cores612vertices128profiles, principaldeficitPOSbothendpoints actualdeficit13POS/entirePOS,PP0. No globalcapacityinference. Formal3 realtail/Eulerprefix raccord compiled atpartialattempt9, finalA7smallcasespending; realtechnicalfailurescaptured. Judge16dispatchcalls hitthreadlimit witholdideatorpendinginit; no Judgeauditstarted, retryafter6FINALslot. NoWin.'
for rel in ['round16/capacity_checks.py','round16/capacity.json','round16/role6/capacity_replay_receipt.json','round16/agent4_formalisation.md','round16/role4/LeastMissingPrimeMargin.lean','round16/role4/final_receipt.json','.arbor/sessions/parity/.coordinator/messages/round16_root_capacity_margin_observation.json']:
    if rel not in cp['previous_goal_turn_evidence']:
        cp['previous_goal_turn_evidence'].append(rel)
cp_path.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
report=root/'REPORT.md'
text=report.read_text(encoding='utf-8')
marker='### Second banc16 et marge harmonique compilée'
assert marker not in text
text+='''
### Second banc16 et marge harmonique compilée

Le second banc neuf passe à son premier essai et dans son unique copie isolée, identique en octets et champs :18 qpremiers parmi201 entiers,34 cœurs,612 points physiques,128 profils réels D/W. Le déficit principal est positif aux deux endpoints de l'enclosure S(N) ; le déficit réel après seules ressources e1/e3 et la somme réelle entière sont positifs. Aucune properpower raw n'apparaît dans cette fenêtre. La capacité favorable ne suffit donc pas ici à payer le corps entier sélectionné. Cela ne réfute pas le signe source A9 ni un futur contrôle asymptotique. Source/gates/reçus sont gelés, le Juge indépendant reste à faire ; root a lu la source et les logs et vérifié les empreintes sans rejouer la banque.

Le rôle4 livre un module Lean neuf compilé dès le premier essai :9 théorèmes,0 nouvelle définition,0 warning et uniquement propext/Classical.choice/Quot.sound. La marge harmonique H_(p−1)(p−2)/(p−1)−logp≥1/144 pour p≥13 et les petits logarithmes sont prouvés sans paramètre S libre. Source e1dbd4f8a68b433c4641c90d6eb12366e7084b0d8b7b7b045b8b11ebd41e6b4a, rapport FINAL4 b12adfa9f03ed0af0735278946ebbf09f9bf41e3a6c4d42cc8912ddedb0097b7. Le rôle3 poursuit le raccord au vrai produit singulier et les petits cas ; ces neuf auxiliaires seuls ne prouvent ni A7 entier ni D_N. Le cumul final indépendant16 est en attente de l'audit, aucune victoire n'est annoncée.
'''
report.write_text(text,encoding='utf-8')
print('ROOT16_CAPACITY_AND_MARGIN_OBSERVATIONS_RECORDED; no bank or Lean invoked.')
