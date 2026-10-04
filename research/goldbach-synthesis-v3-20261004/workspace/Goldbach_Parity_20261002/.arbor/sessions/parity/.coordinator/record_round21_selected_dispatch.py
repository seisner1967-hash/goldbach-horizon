"""Persist actual selected-wave3/4/6 and resolved coordination incidents; no math."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round21'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
prep=read(R/'role3/preparation_receipt.json'); entries=read(R/'role3/preparation_read_manifest.json')['entries']
assert sha(R/'role3/preparation_receipt.json')=='eafb75d6f943687ec74910571bbdc156b84842c1f7ecfe019a7bae4631a5e6f8'
assert sha(R/'role3/preparation_readonly.md')==prep['report_sha256']=='f51ef4a25fbf420fb6897bf29364acb1e0edd6b5bed14362ca777abbb2b5359c'
assert sha(R/'role3/preparation_read_manifest.json')==prep['manifest_sha256']=='897384a68506df9c6dce40c1af55c3e12a5ca8bc1edd02c21e247019240062e3'
assert len(entries)==26 and prep['full_count']==8 and prep['targeted_count']==18
for row in entries: assert sha(Path(row['path']))==row['sha256'],row['path']
roles=[
 {'role':3,'agent':'/root/round21_formal3_prepare','node':'13.13','ownership':['round21/role3/**','round21/agent3_formalisation.md'],'actual_dispatch':'followup_after_actual6dcc08_selection','status':'SOURCEWRITING_NEW_LEAN_ONLY_NO_COMPILER_GATE'},
 {'role':4,'agent':'/root/round21_ideation1_signed','node':'14.6','ownership':['round21/role4/**','round21/agent4_formalisation.md'],'actual_dispatch':'reuse_completed_listed_ROLE1_via_followup_after_actuala9950b_selection','status':'SOURCEWRITING_NEW_LEAN_ONLY_NO_COMPILER_GATE'},
 {'role':6,'agent':'/root/round21_numeric_conservation','nodes':['13.13','14.6'],'ownership':['round21/role6_ap/**','round21/ap.json','round21/role6_reciprocal/**','round21/reciprocal.json'],'actual_dispatch':'followup_selected13.13_then_send_selected14.6','status':'TWO_NEW_BANK_SOURCES_PREPARATION_ONLY_MATH_GATES_CLOSED'}]
obs={'round':21,'status':'ACTUAL_SELECTED_WAVE3_4_6_PERSISTED_ALL_EXECUTION_GATES_CLOSED','recorded_utc':datetime.now(timezone.utc).isoformat(),
 'actual_dispatches':roles,'current_nodes':['13.13','14.6'],'ideation1_2_final_frozen':True,
 'four_concurrency_slots_six_logical_roles_in_waves':True,'independent_Judge5_later':True,
 'coordination_incidents':[{'action':'spawn new round21_formal4_reciprocal','result':'agent thread limit reached','new_agent_created':False},
 {'action':'followup old completed round20_formal4_friable','result':'agent thread limit reached','turn_started':False},
 {'action':'followup currently listed completed round21_ideation1_signed for ROLE4 on ROLE2 branch','result':'success','turn_started':True}],
 'resolved_without_user_input':True,'external_blocker':None,'Lean_or_numeric_execution_authorized':False,
 'preparatory3_full_report_chunk':'953048','preparatory3_full_receipt_chunk':'cf1c17','preparatory3_all26inputsha_verified':True,'victory':False}
(C/'messages/round21_selected_dispatch.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json'); cp.update(phase='ROUND21_SELECTED_ACTUAL3_4_6_SOURCEWRITING_PREPARATION_ALL_MATH_LEAN_GATES_CLOSED',
 in_flight_executors=roles,current_nodes=['13.13','14.6'],external_blocker=None,required_user_input=None)
cp['last_progress']+=' Selectedactualwave3/4/6 persisted: sourceAP13.13, reciprocal14.6, two banksPREPonly. Threadlimit twofailures resolved reusecompletedlistedROLE1asROLE4onROLE2concept; no mathematicalFAIL or externalblocker. APIpreparation3 FULL953048/cf1c17 and26readhashes verified. Judge5later, allmath/Lean21gatesclosed/noWin.'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round21_selected_dispatch.json','round21/role3/preparation_receipt.json']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
p=B/'REPORT.md'; txt=p.read_text(encoding='utf-8'); start=txt.index('**Boucle21 en cours :**'); end=txt.index('\n\n',start)
txt=txt[:start]+'''**Boucle21 en cours :** deux propositions sont figées et sélectionnées.13.13 vise le raccord physique/AP et sa variation d’Abel avec une enveloppe finie réellement construite ;14.6 vise les réciproques non friables de F0\\F1 par projection unique et moment global de tau² dérivé. La conservation unique des3028archives a réellement terminé exit0 le3octobre à05:18:40UTC, sans altération. Les rôles3/4 écrivent les sources Lean et le rôle6 prépare deux bancs neufs stricts N=10^8 ; aucune compilation ni exécution mathématique21 n’est encore autorisée. Les57modules/942théorèmes auxiliaires restent les comptes certifiés ; aucun budget proposé21 n’est encore compilé. Le complément, les capacités et le bilan entier D_N restent ouverts. [Proposition AP](round21/agent1_signed.md), [proposition réciproques](round21/agent2_nonfriable.md).'''+txt[end:]
p.write_text(txt,encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
