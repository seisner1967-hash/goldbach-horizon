"""Record actual FINAL17, feedback and next intake; no mathematical execution."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
import json,subprocess
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator'
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
def read(p):return json.loads(p.read_bytes())
def invoke(cmd,*args):
    p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),cmd,'--cwd',str(B),'--run-name','parity',*args],capture_output=True,text=True,encoding='utf-8')
    if p.returncode:print(p.stdout,p.stderr);raise SystemExit(p.returncode)
m=read(B/'round17/controller_manifest.json');mh=sha256((B/'round17/controller_manifest.json').read_bytes()).hexdigest()
assert mh=='5d20d749aa30bcf939e33cd0f1d1efc1049c85634f6054ae79c81890e6d628a4'
assert m['round']==17 and m['next_protected_artifacts_expected']==997 and not m['victory']
tree=read(C/'idea_tree.json');assert tree['nodes']['13.9']['status']==tree['nodes']['14.2']['status']=='running'
notes={
 '13.9':('agent1_calibrated_typeii.md','typeii_checks.py',
  'FINAL17 independent audit validates full fixed-d77 TypeII finite bank162338integers, actual beta181/theta12460/eight rawproperpowers, six hN/77hN masks, physical caps and true candidate j=v*w with v17/19/503double323 multiplicities analytic only. All6 TypeII functionals NEGfinite, while Gamma theta h1NEG and h3/h39POS; prices E77/L3/L13 theta/II/II_raw are distinct and retained. Written chi13 unit39 calibration cancels one principal and admits qualitative BV-onset-dependent one-mode decay; allcoefficients/fullTypeII/Gamma39 and literal theta calibration price remain unestimated. Exactunit conventions differ and actualoldmask was gcd(b,N), not77. One technical rad(hN) domain failure preserved, unique existing bank replay identical. Valid partial reduction, no wholeD_N/parityWin.'),
 '14.2':('agent2_capacity_incidence.md','role3/SelbergFourForms.lean',
  'FINAL17 independent5newLeancompiles PASS93theorems40defs1instance/134standardaxiomprints; cumul22/337. Actualroots/rho/collisions/saturation and actualMobius Selberg weights/support/normalization/norm/principal1/G derived, no free G or availability. ActualG>=P(y)^4 L_Delta(y)/2 proved with independent analytic prime-log input and scale/coprime/unsat guards, not full sourceC4/Mertens/totient/CRT+1/C6. Fullnewrough201integers9q28cores252physicalvertices47Wimmutable205zeroaxes, A11/R0/S18; true17488CRT/16unsat/10sat checked. Resourcecapacity consumed once; positivewholedeficit unpaid, A/S and globalunion remain open. NewC4annex16cores retains all16subsets and105/210tail, exactmoment,64signs54POS10NEG,6true10falseconditions; all16MarkovPOS and G_P>=halfZ observed, noC4/C6sourcefiniteapplication. Producer23realLeanexit1technical, Judge2preLeanreaderfailures preserved before5freshPASS; no mathematicalparityfailure invented, noWin.')}
for node,(report,code,insight) in notes.items():
    invoke('record','--node-id',node,'--report-file',str(B/'round17'/report),'--score','0','--insight',insight,
           '--result','Independent FINAL17 validates partial actual arithmetic and finite data; global parity bypass and D_N bound remain open.',
           '--code-ref',str(B/'round17'/code))
head=('Goal active, no victory. FINAL17 independent audit3actualattempts exit1,exit1,exit0; two pre-Lean reader errors guard/null corrected in limited continuations without rerunning PASS stages, all originals retained. Five new Lean modules93theorems40defs1instance/134standardaxiomprints, freshindependent5PASS, cumul22modules337aux. Actualfourform roots and arithmeticMobius Selberg weights/support/norm/principal1/G derived; actualG>=P(y)^4 L_Delta(y)/2 under independent prime-log sum and scale/coprime/unsat guards. FullsourceC4/Mertens/totient/CRT+1/C6 notLeanproved. Rough201integers9q28cores252vertices47W205zeroaxes/A11R0S18/17488CRT/10sat16unsat; wholepositive demand/deficit unpaid. TypeII162338fullintegers181beta12460theta8rawpp/sixmasks, realj=v*w17/19/503double323 and distincttheta/II/IIrawprices retained. Onechi13mode writtenonly and additional BVonset; Gamma39/allcoeff/globalcapacity unestimated. Original390strictpositions242POS62NEG86ZERO plusnewC4annex64=54POS10NEG, all16subsets/105210tails,6TRUE10FALSEconditions and16MarkovPOS; no finite1e8sourceonsetusage. Producer30Leaninvocations23technicalexit1/PASS15warning and one numericaldomainfailure retained. 799oldpreserved,143authorinputs/33+15numericbindings/52Judgebindings checked; controller17 binds197+self198 SHA'+mh+'; nextprotected997. Full ledger, sourceonsetu>=10^24, acquiredA7 unchanged. No mathcompiler/numeric/audit rerun byroot.\n')
old=tree['nodes']['ROOT']['insight'].split('\nNext17 must seek')[0]
tail='\nNext18 must seek a genuinely quantitative new estimate for nonrough T_S/T_A after single-consumption physical union, or calibrated whole Gamma/TypeII with literal theta prices, while keeping conditional actualG acquisition. Do not rederive roots/finiteSelberg/truncation/collision or canonical A7. FullC4 analytic conversion can be an explicit remaining task but alone never pays D_N. No equivalent target/availability/orphan premise, no generic projection/norm identity labeled bypass. Fixedledger and997 oldartifacts remain protected; newmath bank only after freshconstraints/newconcept selection.'
invoke('update','--node-id','ROOT','--insight',head+old+tail)
invoke('meta','--set','eval_cmd="'+sys.executable+'" -B -X utf8 "'+str(B/'round17/judge/launch-continuation02-once.py')+'"',
       '--set','dataset_info=FINAL17 actualaudit1,1,0/fresh5LeanPASS;143inputs/33+15numericbindings/454signs;5newmodules93thm40defs1instance;cumul22/337;actualG conditional on prime-log;C4full/C6/A/S/globalopen;sourceu>=10^24;next997;noWin;18intake')
p=C/'checkpoint.json';cp=read(p)
cp.update(phase='ROUND17_COMPLETE_ROUND18_INTAKE',rounds_completed=17,current_nodes=[],in_flight_executors=[],objective_complete=False,victory=False,
          last_judge_receipt='round17/judge/final_receipt.json',last_controller_manifest='round17/controller_manifest.json',
          last_controller_manifest_sha256=mh,next_protected_artifacts_expected=997,next_protected_registry_pending=None,
          next_focus='Quantitative nonrough A/S after physical single-consumption union or whole calibrated Gamma/TypeII with paid literal theta prices.',
          previous_goal_turn_classification='progress',external_blocker=None,last_progress=head.strip())
cp['retained_verified_modules']+=['round17/FourFormRoots','round17/PowersetMoment','round17/SelbergFourForms','round17/FourFormTruncation','round17/FourFormCollisionLoss']
cp['previous_goal_turn_evidence']=list(dict.fromkeys(cp['previous_goal_turn_evidence']+['round17/agent5.md','round17/judge/final_receipt.json',
    'round17/judge/manifest.json','round17/judge/audit_receipt.json','round17/judge/continuation02_receipt.json','round17/controller_manifest.json',
    '.arbor/sessions/parity/.coordinator/messages/round17_feedback.md','.arbor/sessions/parity/.coordinator/messages/round17_nullable_schema_correction.json']))
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
feedback='''# Feedback17 gelé pour18

Acquis Lean neufs : actualrho/racines du vrai F(q)=q(N-eq)(N-q)(N-p0q), rho4 hors vraiDelta, saturation=>cellulevide, vraie fonctionMobius, supportSFtronqué, poidsSelberg dérivés, lambda1=1, norme<=1, principal1/G et erreurfinie visible. Moment des sous-ensembles et queue entière prouvent actualG>=P(y)^4 L_Delta(y)/2 sous sommePremiereLog<=2+2logy et gardes y<=z/logz>=32/32logy<=logz/coprime/unsat. Ne pas ajouter une hypothèse G>=cible ni redériver ces fondations. Mertens/totient, input analytique prime-log, CRT+1 uniforme, constante sourceC4/C6 ne sont pas Lean-certifiés. A7 canonique16 reste acquis. C4 complet seul ne paie pas A/S ni D_N.

SourceFINAL2 partitionexacteA/R/S : au moins unresourcepremier / aucunpremiermaisdeuxzrough / aucunpremieretpetitfacteur. R n'est pas toutl'orphelinat. FiniteN1e8 : A11/R0/S18, wholedeficitPOS ; ressourcesphysiquese1/p0consomméesunefois. C7petitfacteur écrit restebeaucouptropgrand. Sourceonsetu>=10^24 jamaisappliqué ici. GarderLambda(e)surcœurspremiers, wholeU_a/sourceU4, erreurs/branches/axesréels. Gardepetitfacteur : témoinell de n_j, si e≡jmodell alorsθ(N-eq)=0 ; rawproperpowers demeurent, pas effacés.

TypeII chi13 : vraisj=v*w, βsansprimalitéj, calibration unit39 etancienunit3 distinctes. Le coût L13_theta n'est pas L13_II, ni E77_theta/E77_II. Uncoupledecoefficients n'estpas l'ensemble TypeII. BVsurq a son onsetsupplémentaire ; pasN1e8. Les sixT_II sontNEGfinis maisΓ_theta h3/h39POS ; allGamma/wholeTypeII, disponibilité et union restent ouverts. Les503doubles323 gardentune multiplicitéanalytique, pasunenouvelleressourcephysique. Les8rawproperpowers sontretenues.

AnnexeC4 :16cœurs,16sousensembles, produits105/210au-delàde100jamaiscoupés, sommeW/product/momentcoefficients/G_Pinclusionexactes. 6conditionsdemimomentvraies10faussesconservées ;16MarkovPOS, G_P>=Z/2observépourtous16 malgré10gardessuffisantesfausses. Ces10ne sontpasfalsifiers deconclusion niC4source. 64signs54POS10NEG séparés390242POS62NEG86ZERO.

Échecs réels :23Leanexit1techniques/30invocationsauteurs, unPASS15warning corrigéà16, unnumechecdomainerad(hN)avantPASS2. JudgeWindows206avantprocessus puis3audits1,1,0 : flagconditionnelimposétropfort, référencekernelnull205traitéeactive. C_recipe estABSENT205, pasnull ; les analyses anciennes erronées restentfigéesavecclarification. Deuxreprises limitéesdu stadeinachevé, pasdereplaydebanque/W/sign/PASS/anciensoleans/PDF. CinqcompilationsneuvesPASS93thm40defs1instance134axiomsstandards ;22modules337aux. Aucun diagnostic deparité inventé, aucun Win.

997archives protégées pour18 (799 +197pièces17 +controller17). GarderD_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0), Iglobalacquis/sourceonset, rawLambda_Nsansmu², originalalpha/Q/k1, wholeU_a, c1/b1/e1, vraisS(bN), principal-S(N)N, cofacteurslongs, faces/nonbulk, etP5K2/J2surblocentieravantretrait. Ne pasdoublepayerP5/U4, ne pasremplacerladisponibilitéoulepaiementglobalpardesprémisseséquivalentes.
'''
(C/'messages/round17_feedback.md').write_text(feedback,encoding='utf-8')
p=B/'REPORT.md';txt=p.read_text(encoding='utf-8')
txt=txt.replace('au cours de seize boucles','au cours de dix-sept boucles',1)
txt=txt.replace('Dix-sept fichiers Lean ont été compilés puis reconstruits indépendamment, avec244 conclusions auxiliaires distinctes',
                'Vingt-deux fichiers Lean ont été compilés puis reconstruits indépendamment, avec337 conclusions auxiliaires distinctes',1)
txt=txt.replace('La boucle16 ajoute deux modules et36 théorèmes :',
                'La boucle17 ajoute cinq modules et93 théorèmes sur le vrai crible fini, la troncature et une perte de collisions ; son minorant de G garde un input analytique indépendant. La boucle16 ajoute deux modules et36 théorèmes :',1)
txt+='''
### Clôture indépendante17 : vrai G certifié conditionnellement, paiement global ouvert

**Cinq modules recompilés indépendamment sans sorry, erreur ni avertissement ; aucune victoire.** Ils construisent les racines effectives, les poids Selberg avec vraie Möbius et support SF tronqué, puis dérivent lambda1=1, norme<=1 et principal1/G. La saturation donne la cellule vide. Le moment garde toute la queue ; le raccord de collisions donne actualG>=P(y)^4 L_Delta(y)/2 sous un input analytique indépendant de somme première et des gardes explicites. Les93 théorèmes,40 définitions et une instance sont distincts ;134 print axioms n'utilisent que propext/Classical.choice/Quot.sound. Le cumul est22 modules337 théorèmes auxiliaires. La constante C4 source complète, CRT+1 uniforme Lean, C6, A/S, Gamma et le TypeII entier restent ouverts.

Les deux banques nouvelles àN=10^8 et leurs copies isolées existantes sont identiques. Rough :201 entiers9q28cœurs252candidats,47W conservés205axeszéro, partitionA11/R0/S18,10sat16unsat et17488lignesCRT. TypeII :162338entiers181beta12460theta8rawproperpowers,sixmasquesetprixθ/II/II_raw distincts. L'annexe séparée garde les16sousensembles/105210queues,64signs54POS10NEG et6conditionsvraies10fausses. Les390premierssignes242POS62NEG86ZERO restent séparés. Aucune borne asymptotique source n'est appliquée au N fini ; cibleD_N non prouvée.

Les23exit1Lean des30invocations auteurs sont techniques et archivés ;PASS15warning corrigé demeureconservé. Le Juge a deux véritables échecs pré-Lean de lecture de schéma, puis une reprise exit0 : trois audits1,1,0, cinq nouvelles compilationsPASS chacuneunefois, aucune banque/PASS/ancienmodule/W/signe/PDF relancée. Le drapeau d'exclusion n'est vrai que sous sa garde37cas ; kernel_ref estnull205, C_recipe estabsent205. Le rapport final corrige cette précision sans modifier les preuves d'échec.

Root a lu rapports/sources/journaux/reçus puis vérifié143inputs,33+15bindingsnumériques,52bindingsJuge,134axioms,454positions strictes, cinq copies/compilations et799archives, sans exécuter l'audit. Le controller17 lie197pièces et lui-même, pour997archives au prochain préflight. SHAcontroller17: '''+mh+'''. Nodes13.9/14.2 done0, mécanismes valides conservés avec obligations. Les mentions antérieures pendantes sont des observations chronologiques avant gel. Recherche active ; aucun Win ni NoGo global.

Pièces : [SelbergFourForms.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/role3/SelbergFourForms.lean), [FourFormCollisionLoss.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/role4/FourFormCollisionLoss.lean), [Juge17](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/agent5.md), [controller17](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/controller_manifest.json).
'''
p.write_text(txt,encoding='utf-8')
print('ROUND17_RECORDED; next997; no mathematics producer/compiler/audit invoked')
