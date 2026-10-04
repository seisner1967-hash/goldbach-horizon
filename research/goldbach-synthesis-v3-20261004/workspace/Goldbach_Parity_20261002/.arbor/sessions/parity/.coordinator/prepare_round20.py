"""Exact inventory and launch contract20; only metadata, no mathematical execution."""
import json,hashlib
from pathlib import Path
from datetime import datetime,timezone
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002'); C=B/'.arbor/sessions/parity/.coordinator'; R=B/'round20'
def read(p): return json.loads(p.read_text(encoding='utf-8'))
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
controller=B/'round19/controller_manifest.json'; m=read(controller)
assert sha(controller)=='299a605efaa7cf6721e3b65bfea8af976bcbfcdbb1bc841eee6f4a0d9d9d4d08'
old=read(B/'round19/previous_artifacts_sha256.json')['sha256']; assert len(old)==1361
addition=dict(m['bindings_sha256']); assert len(addition)==446
addition['round19/controller_manifest.json']=sha(controller)
assert not set(old)&set(addition); assets=dict(old,**addition)
assert len(assets)==m['next_protected_artifacts_expected']==1808
R.mkdir(exist_ok=False)
registry={'status':'EXACT_INHERITED_PROTECTED_INVENTORY_FOR_ROUND20','file_count':1808,
 'previous1361':1361,'round19_with_controller447':447,'created_utc':datetime.now(timezone.utc).isoformat(),
 'controller19_sha256':sha(controller),'source_previous_registry_sha256':sha(B/'round19/previous_artifacts_sha256.json'),
 'sha256':assets,'preflight_by_numeric_role_pending':True,'numerical_or_Lean_execution_by_root':False}
(R/'previous_artifacts_sha256.json').write_text(json.dumps(registry,sort_keys=True,indent=2)+'\n',encoding='utf-8')
probe='''# PROBE20 — après clôture indépendante19

Recherche autonome active sans limite de cycles utilisateur, aucune victoire. Cadre PDF/ZIP/GitHub et acquis immuables. Six rôles logiques en vagues : idéation1/2, formalisation3/4, Juge5 indépendant, numérique6. Root coordinateur seulement. Nodes13.11/14.4 done0 ; helper report6bd7a1 et check strict6b6a8b ont réellement exit0, vue fraîche constraints c7c1bc intégralement lue :35 findings,5 pruned,maxdepth2. Relire ces contraintes avant chaque IDEATE/sélection et le feedback19, pas une vieille version.

FINAL19 : un audit indépendant unique terminé01:36:25UTC exit0,11 nouveaux modules/185thm/78defs/3structures/268prints standard ; cumul41modules692 auxiliaires. Trois warnings UnitLoss bénins.29 invocations auteurs dont18 FAIL techniques et1 parse Python avantLean, aucun échec ou reprise du Juge. Tous logs/sources/exits conservés ; sorryAx internes de FAIL non admis. Root a vérifié307 inputs,26 dépendances,145 bindings Juge,1361 archives et49281hashes/labels existants. Controller19 lie446pièces plus lui-même, prochain1808. Aucune réexécution routinière d'ancien producteur/Lean/PASS/kernel/log/signe/PDF.

Les identités19 acquises dérivent face3prime avec P/gcd(P,d), normalisation/prix entiers Gamma0=GammaRank+Pi, grands facteurs perdus avec+1, modules<=max(aR,R⁴),32représentations dans UNE expansion, chi réel/totients/IE/effectiveDivisors avec mu0 et estimateur exact autour -Mchi. M réel/X arbitraire n'est pas intrinsèquement positif. Paper K14/Mpositivity garde N/39/d overlap et X=d(L-1)+1,L>=2 ; pas Lean-certifié. P1771 exige gcd(P,N)=1, ne couvre pas tous N. Le signe favorable du prix peut être exactement compensé par GammaRank. OrdinaryAP/exceptions/fronts/combined40/K18/BV/parents/wholeGamma restent impayés.

Les ressources19 utilisent largest real PF/multiplicité, cap/anchor/copremiers réels, tagD/P equalityD, conducteur C<N sans sqrtN, CRT signé dans Z/reconstruction/inverseguards, sourceBracket theta/raw réel, SS minFac<=Z+quotientPrime, sans ordre ajouté. Reindex dans compositeResourceCell/StructuralSupport déclaré seulement, trois strates courte/medium/longue, rawproperpower conservé, µ0/m0 nuls, produits physiques injectifs sousM²>N, harmonique Ω1/2 avec p²/converse. Fullsupport/e1/p0/singletons/parents/capacité/T_A/mediumlong/rangs>=4 etledger restent ouverts. Budget local écrit u>=10^40 ne remplace pas sourceu>=10^24.

Objectif20 : une nouvelle information quantitative sur incidence réelle, ou un paiement réel d'une couche exceptionnelle avec complément et réciproques uniques conservés. Ne pas redériver19calibration/CRT/32counts/IE/H8/racines/normes génériques. Pas de petite Gamma, disponibilité, Hall, targetequivalent ou minoration de capacité en prémisse gratuite. Une nouvelle identité ou un lemme local conditionnel n'est pas Win. Unique preuve de victoire : Lean compile sans sorry ET contenu contourne réellement la parité pour D_N cible, pas seulement PASS syntactique.

Prospectives ROLE1/2 déjà écrites dans C/messages sont des notes papier non sélectionnées/non exécutées, jamais des résultats Lean. ROLE1 : soustraction de masse composite Selberg avec p=minFac(j), j=pv, v>=p, Pminus(v)>=p, q réellement premier. Construire réellement les poids inférieurs, retenir p²/répétitions, vrais AP/endpoints/coefficients et queue hors niveau ; aucun libre transfert BV/Chen. Le diagnostic de principal >4 ne vaut que pour l'idéal Euler leading coefficient avec sa normalisation, pas pour un G asymptotique uniforme non prouvé. ROLE2 : payer absolument les ressources entièrement friables avec cap forçant ressources>=M>=D, préfixe multiset d∈[D,DY], union/classes incompatibles/+1 et Euler/Rankin ; C<N ne force aucune garde de taille. Coûts des demandes F0∨F1 et des réciproques F1 uniques séparés ; m1 non friables de F0\\F1 conservés. La proposition F4 papier au seuilsource n'est pas encore Lean, bridge du domaine source toujours distinct.

Pour IDEATE, utiliser idea_drafting/first_principles_probe, modèles extrêmes, gardes saturées/nonunités/supports vides/longs et coûts décalés. FINAL substantiel + exactement quatre lignes Mechanism:/Hypothesis:/Observable:/Conflicts:, théorème réel, dérivation/budget/onset et nouveau contrat numérique complet N=10^8. Root choisit après lecture FULL/hash et préflight, maxdepth2. Sources techniques niches/nouvelles : browsing primaire obligatoire. Prospective ne doit pas être mutée ; conserver lectureSHA et écrire nouveauxFINAL20 à ownership20.

ROLE6 immédiat : seul préflight nouveau unique1808 (1361+447) et originaux. Ownership round20/conservation.py/json et role6/**. Source/lanceur/snapshots/commande/START PREEXEC puis log/exit/reçu, metadata uniquement. Aucun nouveau banc math ou Lean avant nouvelle sélection/gate root. Après sélection : script neuf strict N=10^8, Fractions/intervalles rationnels rigoroureux zérofloat ; vraie fenêtre complète incluant nonpremiers/axes vides/nonSF µ0/repetitions/longs avant masks, prix literal/D/W/Q/wholeUa/rawproperpower. Y_source auN fini peut être1 : garder garde asymptotique fausse, Ytest distinct explicitement, aucune certification du budget par finiteonset.

ROLE3/4 : nouveau Lean seulement après gate numériquePASS inspectée, imports Judge19/18/16/13 readonly/cache. Chaque réelle erreur est conservée avec code exact/commandes/log/exit ; correction après FAIL seulement, pas replay PASSinchangé. Construire les objets arithmétiques véritables, pas coefficients libres ni hypothèse de l'estimation cible. ROLE5 après tous FINAL : audit indépendant de données stockées/bytes et nouvelle compilation seulement, aucun olean auteur20, pas de signe/log/numericproducer recalculé. Geler avant gate distincte root après FULL sources/prep. Toute FAIL réelle stop ; continuation limitée après diagnostic, jamais stagePASS rejoué.

Notations fixed : u=logN,ell=logu,alpha=ceilN1/4,Q=floor((N-1)/alpha),a=ceilN7/16,M=ceilN3/4,Boriginal=ceilN1/64. Sourceu>=10^24 jamais1024 ; N=10^8 boussole seulement. Ddivisoriel≠D_N ; Wkernel≠-Wkernel. RawLambda_N conserveproperpowers sansµ(n)^2. A7 vraiS(N)-logp0>=1/144 sousC2acquis préservé, aucune incidence gratuite. Ledger D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0). Iglobal/acquis/Q/k1/wholeUa/c1b1e1/vraiS(bN)/principal-S(N)N/longs/faces/nonbulk/P5K2J2blocentier avant retrait, U4 alternatif sans double paiement conservés.

Runtime déjà prêt : Python C:/Users/Utilisateur/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe SHA4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c. Lean4.15 C:/Users/Utilisateur/.elan/toolchains/leanprover--lean4---v4.15.0/bin/lean.exe SHA8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08. Cacheq356 mathlib commit9837ca9d65d9de6fad1ef4381750ca688774e608/huitlibs. Aucune installation/sonde/version/relecturePDF nécessaire.
'''
(R/'PROBE_BLOCK.md').write_text(probe,encoding='utf-8')
obs={'status':'ROUND20_FRESH_CONSTRAINTS_INTAKE_PREPARED','created_utc':datetime.now(timezone.utc).isoformat(),
 'helper_report_exit':0,'helper_check_strict_exit':0,'fresh_constraints_full_read_chunk':'c7c1bc',
 'validated_findings':35,'pruned_directions':5,'max_depth':2,'protected_files':1808,
 'registry_sha256':sha(R/'previous_artifacts_sha256.json'),'probe_sha256':sha(R/'PROBE_BLOCK.md'),
 'new_nodes_selected':False,'new_numeric_or_Lean_started':False,'victory':False}
(C/'messages/round20_intake.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
cp=read(C/'checkpoint.json'); cp.update(phase='ROUND20_PROBE_READY_UNIQUE_CONSERVATION_PENDING',next_protected_registry_pending='round20/previous_artifacts_sha256.json')
cp['last_progress']+=' Feedback19/report/check strict0 and fresh35constraints read; exact1808 registry/PROBE20 prepared. Two prospectivepaper notes are not selected/results; new20nodes/banks/Lean not launched. Unique conservation20 next,noWin.'
cp['previous_goal_turn_evidence']+=['round20/PROBE_BLOCK.md','round20/previous_artifacts_sha256.json','.arbor/sessions/parity/.coordinator/messages/round20_intake.json']
(C/'checkpoint.json').write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs,indent=2))
