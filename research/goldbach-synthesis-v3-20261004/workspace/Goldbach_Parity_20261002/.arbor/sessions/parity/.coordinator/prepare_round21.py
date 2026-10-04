"""Prepare exact protected inventory and contract21; metadata only."""
import json,hashlib,sys,subprocess
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round21'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
controller=B/'round20/controller_manifest.json'; m=read(controller)
assert sha(controller)=='815d2ce77851a01d9addfa4202a17edb787a42f7f080d4e41cab18aa7b002b04'
old=read(B/'round20/previous_artifacts_sha256.json')['sha256']; assert len(old)==1808
addition=dict(m['bindings_sha256']); assert len(addition)==1219
addition['round20/controller_manifest.json']=sha(controller)
assert not set(old)&set(addition); assets=dict(old,**addition)
assert len(assets)==m['next_protected_artifacts_expected']==3028
R.mkdir(exist_ok=False)
registry={'status':'EXACT_INHERITED_PROTECTED_INVENTORY_FOR_ROUND21','file_count':3028,'previous1808':1808,'round20_with_controller1220':1220,
 'created_utc':datetime.now(timezone.utc).isoformat(),'controller20_sha256':sha(controller),
 'source_previous_registry_sha256':sha(B/'round20/previous_artifacts_sha256.json'),'sha256':assets,
 'preflight_by_numeric_role_pending':True,'numerical_or_Lean_execution_by_root':False}
(R/'previous_artifacts_sha256.json').write_text(json.dumps(registry,sort_keys=True,indent=2)+'\n',encoding='utf-8')
probe='''# PROBE21 — après FINAL20 réellement clos

Recherche autonome active, aucune limite de cycles utilisateur, aucune victoire. Cadre PDF/ZIP/GitHub et acquis fixés. Six rôles logiques en vagues, quatre places : idéation1/2, formalisation3/4, Juge5 indépendant, numérique6. Root coordinateur seulement, jamais auteur de preuve/script math/Juge exécutant. Nodes13.12/14.5 done0. Helper report f6ff3d et check strict7825a4 exit0. Vue fraîche constraints bbd2ff intégralement lue :37 findings,5 pruned,maxdepth2. Chaque agent doit appeler puis lire sa propre vue fraîche TreeView constraints juste avant IDEATE ; toute sélection root attend conservation nouvelle unique3028 et FINAL conceptuel lu/hashé.

FINAL20 : audit indépendant unique04:42:00..04:52:05UTC exit0,16 nouveaux modules/250thm/83defs/1structure/334prints standards/13warnings bénins ; cumul57modules942théorèmes auxiliaires.38 invocations auteurs16PASS22FAIL techniques archivées ; pas d'erreur analytique inventée. Deux banques nouvelles N=10^8 ont chacune un PASS unique, sourceguardsFALSE. Controller20 lie1219pièces plus lui-même1220, précédent1808→3028. Toutes2837entrées uniquesJuge et189finalbindings vérifiées. Les14 extras documentaires/archives géométrie sont explicitement préservés sans crédit de nouveau PASS. CP1252 et révisions NON_EXECUTED demeurent distinctes des FAIL Lean.

Acquis20 à importer sans les redériver : Bonferroni impair sur réelle primoriale, somme binomiale ; minFac composite avec p²/répétitions/p|v/nonminimalnegative ; Selberg réellement construit lambda1=1,Q=1/G ; PhysicalWitness18 q premier avant Prime(j), soustraction ALLcomposites avec PP/raw conservés ; conducteur nu=p*lcm(h,K/gcd(K,p)), nonunités/incompatibilités/caps/fronts ; actualAP remainder=mass−main, identité Ttheta=mainQ−mainC+(RQ−RC)−Tail−Slack ; C(eq) réel/multiset prefix/2AP+1/Euler-Rankin/tau/TK ; agrégation toutes fibres H19 et réciproques F1 image q unique ; sourceGeometry logN>=10^24 seul derivefloors/ceilsguards.

Acquis source véritable : sourceFriableAbsoluteCost = somme thetaABS sur H19∩(F0∨F1) + somme des sourceBracket(q,N−q)ABS sur image(H19∩F1), <=N/(8192*u*ell). Aucun smallsum/TK/capacité/cible gratuit en prémisse. C'est un budget PARTIEL déjà indépendant PASS, pas tout D_N. Les enveloppes raw sont locales, le budget agrégé est theta. F0\\F1 demande theta déjà payée, mais réciproque m1 nonfriable impayé. Complément où deux ressources P+>Y sans OmegaBound impayé.

Obligations21 littérales : A composite B6variation/endpoints/bijectionAP source, SD et constantes/onsets BV effectifs, comparaison principale source et contrôle utile queue/slack/moduleshorsniveau ; B bridge M0 littéral acquis (reference_price porte encore M0 arbitraire), kappa et frame-source/agrégation ; C réciproques F0\\F1 nonfriables et complément ; D H19→sourcefrontière entier, e1/p0/singletons/faces/nonbulk/medium/long/nonSS et partitioncroisée ; E union tous vertices/demandes, parents/vrais W/intersections/consommation unique/Gamma/T_A ; F sixpostes D_N entiers. Do not rederive20 proofs/local identities or old Selberg/CRT/Gram/calibration/norm/32counts/H8/A7, and do not relabel a conditional algebraic identity as a bypass. Favor actual new quantitative information on an unpaid object. A bounded necessary source bridge or partial analytic lemma can be pursued honestly, never counted as WIN alone.

ROLE1 objectif directionnel : incidence composite réellement signée, distribution AP à décalage N/coefficients réels, ou bridge principal/poids réel qui élimine une obligation précise. ROLE2 objectif directionnel : réciproques nonfriables de F0\\F1, complément réel ou couverture/sourcecapacity physique sans crédit gratuit. Chacun fait cinq candidats/first_principles_probe, gardes saturées/nonunités/supports vides/répétitions/mediumlong/coûts décalés ; auto-filtre shallowtweaks et mécanismes pruned. FINAL substantiel, dérivation réelle/onset/budget et exactement quatre lignes Mechanism:/Hypothesis:/Observable:/Conflicts: pour noeud maxdepth2. Fournir théorème concret Lean, liste imports readonly et nouveau contrat numérique complet N=10^8, sans exécuter Lean/math. Root lit FULL puis sélectionne après préflight. Aucun SD/Gamma petit, disponibilité/Hall/Omega/target-equivalent en prémisse gratuite ; no asymptotic claimed from finite test. Sources nouvelles techniques/niches : browsing primaire obligatoire, attribution précise.

ROLE6 immédiatement : seul nouveau préflight de conservation unique3028 et2originaux, metadataSHA/inventaire uniquement. Ownership round21/conservation.py/json et round21/role6/**. Préparer source+lanceur+préparation et s'arrêter PREPARED pour rootFULL/hash/gate ; puis START réel/captures PREEXEC/commande/log/exit/reçu. Zéro ancien banc/Lean/PASS/signe/log/kernel/PDF exécuté. Après sélection et gate distinctes seulement : script STRICT NEUF N=10^8, Fractions/intervalles rationnels zérofloat, fenêtre entière avantprime/masks, axes vides/nonSFµ0/repeatedPF/nonunits/longs/caps/AP+1/prix literal/Q/wholeUa/rawPP, réciproquesphysiques uniques. Finite sourceseuil FALSE/Ysource1 versus Ytest explicite. Ne pas recopier/rejouer de vieux banc pour en annoncer un nouveau résultat.

ROLE3/4 ultérieurement : nouveaux fichiers Lean seulement après gate numériquePASS rootinspectée et nouvelles sources/builder/prep FULL/hash ; historical Judge20/19/18/16/13 imports readonly/cache, zéro recompile ancienPASS. Chaque réelle erreur exactsource/command/log/exit est figée ; correction après FAIL seulement. Objets arithmétiques construits, aucune hypothèse déguisée de cible. #print axioms de chaque déclaration explicite qualifiée ; no sorry/admit/axiom ajouté/unsafe/native_decide/nonstandardaxiom. ROLE5 indépendant après tousFINAL : read-only audit des bytes et certificats stockés, nouvelle compilation des seuls nouveaux modules, aucun olean auteur21 et aucune rerun numericproducer/logarithms/signs. PREPARED/gate séparée root; uniqueactualJudgePASSstop, vraieFAILdiagnosticcontinuation bornée sansstagePASSreplay.

Notations fixed : u=logN,ell=logu,alpha=ceilN1/4,Q=floor((N−1)/alpha),a=ceilN7/16,M=ceilN3/4,Boriginal=ceilN1/64. Source u>=10^24 JAMAIS1024. Budget local écrit10^40 ne paie pas gratuitement segmentsource. N=10^8 boussole : alpha100,Q999999,a3163,M1m, gardes asymptotiques fausses. Ddivisoriel≠D_N ; Wkernel≠−Wkernel ; wholeUa≤a incl≤alpha et k1/Nmask ; rawLambda_N sansµ(n)^2, PP conservées. Acquis Iglobal/A7canonicalp0/S(N)−logp0>=1/144 sous C2box2541/4096..11011/16384 immuables. Ledger D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0). c1b1e1,vraiS(bN),principal−S(N)N,longs/faces/nonbulk, P5K2J2blocENTIER avant retraite et U4alternatif sans doublepaiement conservés.

WIN CONDITION : seul .lean compilé sans sorry avec contenu réellement nouveau qui contourne la parité pour les objetsfixés D_N et cible ; PASSsyntaxique auxiliaire/conditionalgeneric/localbudget ou testPython ne donne jamaisvictoire. Tout échec réel est documenté honnêtement; la difficulté math n'est pas un blockerexterne. Continuer autonomement les cycles nécessaires.

Runtime prêt, aucune installation/sonde/version/relecturePDF : Python C:/Users/Utilisateur/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe SHA4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c ; Lean4.15 C:/Users/Utilisateur/.elan/toolchains/leanprover--lean4---v4.15.0/bin/lean.exe SHA8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08 ; cacheq356mathlib commit9837ca9d65d9de6fad1ef4381750ca688774e608,huitlibs. UTF8 et -B. Root garde rapport/coordinator fichiersC, agents ownership21 distinctes, aucune écriture old3028/.git. Aucun PR/push/message externe.
'''
(R/'PROBE_BLOCK.md').write_text(probe,encoding='utf-8')
obs={'status':'ROUND21_FRESH_CONSTRAINTS_INTAKE_PREPARED','created_utc':datetime.now(timezone.utc).isoformat(),
 'helper_report_exit':0,'helper_report_chunk':'f6ff3d','helper_check_strict_exit':0,'helper_check_chunk':'7825a4',
 'fresh_constraints_full_read_chunk':'bbd2ff','validated_findings':37,'pruned_directions':5,'max_depth':2,
 'protected_files':3028,'registry_sha256':sha(R/'previous_artifacts_sha256.json'),'probe_sha256':sha(R/'PROBE_BLOCK.md'),
 'new_nodes_selected':False,'new_numeric_or_Lean_started':False,'victory':False}
(C/'messages/round21_intake.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
# Planned eval metadata must point to21 before any new executor prompt; this is not authorization or execution.
H=Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
p=subprocess.run([sys.executable,'-B','-X','utf8',str(H),'meta','--cwd',str(B),'--run-name','parity',
 '--set','eval_cmd="'+sys.executable+'" -B -X utf8 "'+str(R/'judge/run_once.py')+'"',
 '--set','dataset_info=ROUND21 intake;3028protected;sourceu>=1e24;57modules942aux;noWin;fresh37constraints;no math yet'],capture_output=True,text=True,encoding='utf-8')
assert p.returncode==0,(p.stdout,p.stderr)
cp=read(C/'checkpoint.json'); cp.update(phase='ROUND21_PROBE_READY_UNIQUE_CONSERVATION_PENDING',next_protected_registry_pending='round21/previous_artifacts_sha256.json',
 current_protected_artifacts=3028,current_protected_registry='round21/previous_artifacts_sha256.json',current_protected_registry_sha256=obs['registry_sha256'])
cp['last_progress']+=' Feedback20/report/check strict0 and fresh37constraints FULLbbd2ff; exact3028 registry/PROBE21 prepared. Eval planned21 updated before selection, not math authorization. Uniqueconservation21 next, newnodes/banks/Leanclosed/noWin.'
cp['previous_goal_turn_evidence']+=['round21/PROBE_BLOCK.md','round21/previous_artifacts_sha256.json','.arbor/sessions/parity/.coordinator/messages/round21_intake.json']
(C/'checkpoint.json').write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs,indent=2))
