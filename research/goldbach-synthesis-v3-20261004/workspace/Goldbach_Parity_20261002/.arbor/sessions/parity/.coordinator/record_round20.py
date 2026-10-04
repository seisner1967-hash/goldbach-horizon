"""Record frozen FINAL20, update durable reports; no math/compiler/audit execution."""
import sys,json,subprocess,hashlib
from pathlib import Path
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def invoke(command,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),command,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode: print(p.stdout,p.stderr); raise SystemExit(p.returncode)
controller=B/'round20/controller_manifest.json'; m=read(controller); digest=hashlib.sha256(controller.read_bytes()).hexdigest()
assert digest=='815d2ce77851a01d9addfa4202a17edb787a42f7f080d4e41cab18aa7b002b04'
assert m['next_protected_artifacts_expected']==3028 and not m['victory']
tree=read(C/'idea_tree.json'); assert tree['nodes']['13.12']['status']==tree['nodes']['14.5']['status']=='running'
notes={
 '13.12':('agent1_switched_composite.md','role3/SwitchedIncidenceEstimator.lean',
  'Independent FINAL20 six composite modules prove actual odd Bonferroni/minFac lower weights, constructed Selberg lambda1/G, physical q-prime composite subtraction with proper powers, exact conductor p*lcm(h,K/gcd(K,p)), nonunits/caps/fronts and signed actual AP remainders=mass-main; full identity retains Tail/Slack. Source B6 variation/window bijection, SD/effective BV, principal source comparison, weighted kappa aggregation and literal M0 bridge remain unproved. Five finite Gamma theta/raw NEG accompany five principal-minus-M0 POS; source guards false, no sign transfer. 91 new thms/50defs/141 standard prints, 14 author Lean actuals/8 technical FAIL; fresh independent Judge six PASS. Score0, no parity bypass.'),
 '14.5':('agent2_friable.md','role4/FriableSourceBudget.lean',
  'Independent FINAL20 ten friable modules including source geometry derive repeated-prime prefix, actual Euler/Rankin/tau/TK, two AP +1 fronts, all-rank demand aggregation and unique F1 reciprocal images. Source onset logN>=10^24 alone derives guards/floors/ceils and sourceFriableAbsoluteCost on H19 intersect (F0 union F1) plus unique F1 reciprocal ABS <=N/(8192 logN loglogN). No free small sum or capacity premise. F0 minus F1 nonfriable reciprocal, both-nonfriable complement, H19 whole-source bridge/cross-partition/capacities/parents/Gamma/TA/fullledger remain open; aggregated budget theta, raw envelopes local. 159 newthms/33defs/1structure/193prints,24actualauthorLean14technicalFAIL; independent ten freshPASS. Score0, no parity bypass.')}
for node,(report,code,insight) in notes.items():
    invoke('record','--node-id',node,'--report-file',str(B/'round20'/report),'--score','0',
      '--insight',insight,'--result','Actual independent FINAL20 PASS auxiliaries and partial source friable cost; global parity bypass and fixed D_N target open.',
      '--code-ref',str(B/'round20'/code))
head='FINAL20 closed: actual unique independent audit 04:42:00..04:52:05UTC exit0,16freshLeanPASS/0FAIL,250thm83defs1structure334standardprints13benignwarnings; cumulative57modules942auxiliarythms. Authors38actualLean16PASS22technicalFAIL, two new N1e8banks uniquePASS0replay/sourceguardsfalse. True sourcefriable cost<=N/(8192uell) from sourceu>=1e24, no full ledger/parity Win. All2837uniqueJudgeinputs/189Judgefinalbindings/1808previous unchanged;1219roundfiles+self1220next3028, controllerSHA'+digest+'. Root bytes/receipts/storedlabels only, zero proof/compiler/audit/producer/logsign execution. '
tail='Next21: new quantitative information on actual composite prime incidence/distribution, or cover remaining nonfriable reciprocal/complement with real unique capacities and source support. Preserve source u>=1e24, literal M0/kappa, q primality, PP, Q/k1/wholeUa/allfronts/full D_N ledger. Do not rederive20 Bonferroni/Selberg/AP identities or friable Euler/TK/sourcebudget; no small SD/Gamma/availability/Hall/target-equivalent assumption. Fresh constraints and unique3028 conservation before new selection/banks; six logical roles in four slots, no parityWin.'
invoke('update','--node-id','ROOT','--insight',head+'\n'+tree['nodes']['ROOT']['insight']+'\n'+tail)
invoke('meta','--set','eval_cmd="'+sys.executable+'" -B -X utf8 "'+str(B/'round20/judge/run_once.py')+'"',
 '--set','dataset_info=FINAL20 actualuniqueaudit0/16freshLeanPASS;250thm83defs1str334prints;cumul57/942;1808preserved,next3028;partialsourcefriable<=N/(8192uell);SD/M0/nonfriable/support/capacity/fullledger open;noWin;21intake')
cp=read(C/'checkpoint.json'); cp.update(phase='ROUND20_COMPLETE_ROUND21_INTAKE',rounds_completed=20,current_nodes=[],in_flight_executors=[],
 objective_complete=False,victory=False,last_judge_receipt='round20/judge/final_receipt.json',last_controller_manifest='round20/controller_manifest.json',
 last_controller_manifest_sha256=digest,next_protected_artifacts_expected=3028,next_protected_registry_pending=None,
 previous_goal_turn_classification='progress',external_blocker=None,last_progress=head+tail)
new=['round20/'+r['module'] for r in read(C/'messages/round20_judge_finish_root_observation.json')['independent_module_receipt_observations']]
assert not set(new)&set(cp['retained_verified_modules']); cp['retained_verified_modules']+=new
assert len(cp['retained_verified_modules'])==57
cp['source_geometry_executor']['status']='FINAL_AUXILIARY_GEOMETRY_INDEPENDENT_PASS_CLOSED20'
cp['previous_goal_turn_evidence']+=['round20/agent5_judge.md','round20/judge/final_receipt.json','round20/judge/final_manifest.json','round20/adjudication.json',
 'round20/controller_manifest.json','round20/ideation_failure_feedback20_final.md','.arbor/sessions/parity/.coordinator/messages/round20_judge_finish_root_observation.json']
(C/'checkpoint.json').write_text(json.dumps(cp,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
feedback='# Feedback20 et obligations pour21\n\n'+head+'\n\n'+notes['13.12'][2]+'\n\n'+notes['14.5'][2]+'\n\n'+tail+'''\n\n
Les22 FAIL Lean auteurs réellement exécutés sont techniques et archivés avec leur source/command/log/exit. Aucun FAIL n'est inventé au Juge, aucun sorryAx de déclaration échouée n'est crédité. CP1252 après réception sauvegardée et révisions de schémas/lanceurs NON_EXECUTED restent distincts des FAIL Lean. Zéro réexécution de PASS/ancien producteur/sign/log/PDF.

Obligations21 : (A) B6/SD/distribution AP uniforme/onsets BV, vrais restes, fronts/slack/queue horsniveau ; (B) M0 littéral acquis, kappa et frame-source ; (C) réciproques F0\\F1 nonfriables et complément deux P+>Y sans borne Omega ; (D) H19 vers support frontière entier, e1/p0/singletons/faces/nonbulk/medium/long/nonSS/partitioncroisée ; (E) union tous vertices/demandes, parents/vrais W/intersections/consommation unique/Gamma/T_A ; (F) six postes D_N, Q/k1/wholeUa/rawPP/Bpp payé une fois. Le budget source theta est partiel ; les raw bounds sont locales. Seule une réelle information de parité reliée aux termes fixés peut permettre la victoire.

Source : logN>=10^24. Annexes N=10^8 : gardes source FALSE, Ysource=1/Ytest=4096, fenêtre composite test au-delà N/4. Cinq principaux-minus-M0 POS et cinq Gamma theta/raw NEG sont des certificats finis, aucun transfert au source. Aucun budget local seuil10^40 ne règle gratuitement le segment depuis10^24. Acquis Iglobal/A7/C2 conservés, D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0), P5 entier avant retrait/U4 alternatif sans double paiement.
'''
(C/'messages/round20_feedback.md').write_text(feedback,encoding='utf-8')
p=B/'REPORT.md'; txt=p.read_text(encoding='utf-8')
assert 'au cours de dix-neuf boucles' in txt
txt=txt.replace('au cours de dix-neuf boucles','au cours de vingt boucles',1)
txt=txt.replace('Quarante et un fichiers Lean ont été compilés puis reconstruits indépendamment, avec692 conclusions auxiliaires distinctes','Cinquante-sept fichiers Lean ont été compilés puis reconstruits indépendamment, avec942 conclusions auxiliaires distinctes',1)
start=txt.index('**Boucle20 — auteurs clos, Juge indépendant en cours :**'); end=txt.index('\n\n',start)
paragraph='''**Boucle20 close :** seize nouveaux modules ont été compilés indépendamment sans sorry,250 théorèmes,83 définitions,1 structure et334 prints d’axiomes standards. L’audit unique a terminé le3octobre à04:52:05UTC avec exit0 et13 warnings bénins. Les22 FAIL techniques des38 invocations auteurs sont conservés. Les six modules composites construisent les vrais poids et l’identité avec queue, slack et restes AP ; les dix modules friables prouvent le coût theta déclaré sur H19∩(F0∨F1) plus les réciproques F1 uniques ≤N/(8192 logN loglogN), sous le seul seuil source logN≥10^24. Les réciproques non friables F0\\F1, le complément, le pont au support entier, SD/M0, Gamma/capacités et tout le bilan D_N restent ouverts. Les deux bancs N=10^8 ont un exit0 unique avec gardes source fausses. Cumul57 modules/942 théorèmes auxiliaires ; aucune victoire. [Rapport indépendant](round20/agent5_judge.md), [budget source partiel](round20/role4/FriableSourceBudget.lean), [feedback](round20/ideation_failure_feedback20_final.md), [controller20](round20/controller_manifest.json).'''
txt=txt[:start]+paragraph+txt[end:]
txt+='\n\n### Clôture20 et recherche21\n\n'+head+'\n\n'+notes['13.12'][2]+'\n\n'+notes['14.5'][2]+'\n\n'+tail+'\n'
p.write_text(txt,encoding='utf-8')
print('ROUND20_RECORDED;57modules942aux;next3028;noWin;no math/Lean/audit/producer execution')
