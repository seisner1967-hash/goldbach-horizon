"""Persist actual role1/2/6 dispatches21; metadata only."""
import json
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
roles=[
 {'role':1,'agent':'/root/round21_ideation1_signed','ownership':['round21/role1/**','round21/agent1_signed.md'],'status':'ACTUALLY_SPAWNED_IDEATE_AFTER_OWN_FRESH_CONSTRAINTS_NO_MATH'},
 {'role':2,'agent':'/root/round21_ideation2_complement','ownership':['round21/role2/**','round21/agent2_nonfriable.md'],'status':'ACTUALLY_SPAWNED_IDEATE_AFTER_OWN_FRESH_CONSTRAINTS_NO_MATH'},
 {'role':6,'agent':'/root/round21_numeric_conservation','ownership':['round21/role6/**','round21/conservation.py','round21/conservation.json'],'status':'ACTUALLY_SPAWNED_METADATA_PREPARATION_ONLY_GATE_CLOSED'}]
obs={'round':21,'recorded_utc':datetime.now(timezone.utc).isoformat(),'actual_dispatches':roles,
 'six_logical_roles':True,'four_concurrency_slots':True,'role3_4_5_later_waves':True,
 'new_nodes_selected':False,'new_math_or_Lean_authorized':False,'new_conservation_authorized':False,'victory':False}
(C/'messages/round21_dispatch.json').write_text(json.dumps(obs,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json'; cp=json.loads(p.read_text(encoding='utf-8'))
cp.update(phase='ROUND21_IDEATION1_2_ACTIVE_CONSERVATION_PREPARATION_GATE_CLOSED',in_flight_executors=roles,current_nodes=[],
 objective_complete=False,victory=False,external_blocker=None,required_user_input=None)
cp['last_progress']+=' Actualspawn21ROLE1signed/ROLE2nonfriable/ROLE6metadata preparation, eachideator ownfreshconstraints;1/2notselected, allmath/Lean/conservationgatesclosed;3/4/5laterwaves.'
cp['previous_goal_turn_evidence']+=['.arbor/sessions/parity/.coordinator/messages/round21_dispatch.json']
p.write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
report=B/'REPORT.md'; txt=report.read_text(encoding='utf-8')
marker='**Boucle21 en cours :** les deux agents d’idéation cherchent une estimation nouvelle pour l’incidence composite signée et le complément non friable. Le préflight de conservation des3028archives est en préparation, sans ancien calcul rejoué. Aucun nouveau nœud, banc mathématique ou Lean21 n’est encore sélectionné ou exécuté. Les57modules/942théorèmes auxiliaires et la borne friable source partielle restent acquis ; victoire=false.\n\n'
assert '**Boucle21 en cours :**' not in txt
idx=txt.index('**Boucle20 close :**'); report.write_text(txt[:idx]+marker+txt[idx:],encoding='utf-8')
print(json.dumps(obs,ensure_ascii=False,indent=2))
