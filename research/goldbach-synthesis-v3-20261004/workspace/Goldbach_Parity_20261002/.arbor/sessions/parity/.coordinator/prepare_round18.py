"""Round18 intake contract and exact inherited inventory; no numerical test."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json
B=Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
C=B/'.arbor/sessions/parity/.coordinator';R=B/'round18'
def read(p):return json.loads(p.read_bytes())
def h(p):return sha256(p.read_bytes()).hexdigest()
m=read(B/'round17/controller_manifest.json')
assert h(B/'round17/controller_manifest.json')=='5d20d749aa30bcf939e33cd0f1d1efc1049c85634f6054ae79c81890e6d628a4'
old=read(B/'round17/previous_artifacts_sha256.json')['sha256'];assert len(old)==799
addition={'round17/'+name:value for name,value in m['bindings_sha256'].items()}
addition['round17/controller_manifest.json']=h(B/'round17/controller_manifest.json')
assert len(addition)==198 and not set(old)&set(addition)
assets=dict(old,**addition);assert len(assets)==997
R.mkdir(exist_ok=False)
registry={'status':'EXACT_INHERITED_PROTECTED_INVENTORY_FOR_ROUND18','file_count':997,'previous799':799,'round17_with_controller198':198,
          'created_utc':datetime.now(timezone.utc).isoformat(),'controller17_sha256':h(B/'round17/controller_manifest.json'),
          'source_previous_registry_sha256':h(B/'round17/previous_artifacts_sha256.json'),'sha256':assets,
          'preflight_by_numeric_role_pending':True,'numerical_or_Lean_execution_by_root':False}
(R/'previous_artifacts_sha256.json').write_text(json.dumps(registry,indent=2,sort_keys=True)+'\n',encoding='utf-8')
probe='''# PROBE BLOCK — boucle18 après clôture17

Cadre et acquis maintenus. Goal actif, aucun Win. Root a lu frais les contraintes après FINAL17 :31findings,5directionspruned, maxdepth2 ; helper report puischeckstrict réellementexit0. Les nodes13.9/14.2 sontdone0. Lire messages/round17_feedback.md, REPORT.md, les FINAL17/16 pertinents, puis une vue fraîche constraints avant IDEATE. Ne pas redériver ce qui est acquis. Seul un contournement de parité effectif dans un Lean sanssorry, nonconditionné par une disponibilité/masse/paiement équivalente àD_N, peut gagner ; PASS auxiliaire seul reste score0.

Acquis nouveaux :5modules93thm40defs1instance,134axiomsstandards, indépendants ; cumul22/337. Vraies racines/rho/saturation/collisions, Möbius arithmétique, supportSF tronqué, inversionSelberg/poids/norme/principal1/G, moment avec queue conservée, vraie minorationG>=P(y)^4 L_Delta(y)/2 conditionnée par inputindépendant sum(logp/p)<=2+2logy et gardes y<=z/logz>=32/32logy<=logz/coprimalités/non-saturation. Input analytique, Mertens/totient, CRT+1 uniforme et C4sourcecomplet/C6 restent NONLeancertifiés. A7canonique16 réel S(N)-logp0>=1/144 sous enclosureC2 acquise reste acquis ; aucune masse d'incidences premières n'en découle.

Objectif18 : produire un mécanisme quantitatif nouveau portant sur le complémentnonrough T_S et/ou la capacité T_A après unionphysique, ou sur Gamma/TypeII entier calibré avec prixθpayés. Une nouvelle norme/projection/identitéfinie ou conversionC4 seule n'est pas un contournement. R n'est pas toutl'orphelinat ; l'uniondesparents doit consommer chaquevertexunefois. Les branchesΛ(e), e1/p0, rawproperpowers et erreurs duvraiW restent explicites. Ne pas faire d'une famille d'incidences nonvide/dense une prémisse gratuite ; ne pas poser le minorant/l'upperbound désiré commehypothèse. Ne pas interpréter les trois falsifiersfinis locaux commeunNoGo source ou global.

Rôle1 — idéation quantitative bilinéaire : partir des vraisj=v*w, βsansfiltrepremierj et de Gamma calibré. Le modeχ13(v)χ13(w) fixé resteunseulmode écrit, àonsetBVsupplémentaire. Le prixL13_theta est différent de L13_II et deE77 ; lesθΓh3/h39 sontPOSfinis malgréTII NEG. Chercher un nouveau mécanisme qui contrôle le poids/calibration physique complet et respecte les plages de facteurs du candidat, pas seulement ducomplément. Une hypothèse technique indépendante doit être identifiée avec son prix/onset, pas assimilée àla cible.

Rôle2 — idéation quantitative incidence/nonrough : partir de partitionexacte A/R/S et duvraiDelta. Pour S, témoinell diviseN-jq ; e≡jmodell forceθ(N-eq)=0 mais raw reste. Les cas restantes et collisions/Γ/poidsμ gardent leur masse signée. Le crible4formes paie une sousfamilleR, pasA/S. Chercher un mécanisme arithmétique nonstandard payant le défaut global ; aucune simpleaméliorationdeconstante,z,w, choixdepetitpremier ou gratuitéHall/Poisson n'est suffisante.

Chaque idéateur doit appliquer idea_drafting/first_principles_probe : tester les modèles extrêmes et les classes de conflits, préciser ce qui ferait passer la frontière et ce que le compilateur doit réellement établir. Fournir un FINAL conceptuel substantiel et exactement4lignes Mechanism:/Hypothesis:/Observable:/Conflicts: pour le futurTreeAddNode, avec une estimation ou obligationquantitative indépendante explicite, limites/sourceonsets et contrat de falsification neuf. Aucun node ni banque n'est sélectionné avant lecture root. Maxdepth2 : éventuel13.10ou14.3 sousparents13/14, jamaisenfantdepth3 de13.9/14.2. Ne pas choisir eux-mêmes l'id.

Rôles3/4 seulement après candidat sélectionné : théorème concret Lean surlesobjetsréels, dépendances17 enlecture etaucunoldPASSrebuild ; conserverchaquesnapshot/log/exit réel. Jugeindépendant ensuitefreezeFINAL/inputs,compileneufseulement,auditstocké ; conservergardesconditionnelles/champsnull/absents au lieud'inventerschéma. Les erreursd'API/lecteurs restent techniques, jamaisune faussedéduction deparité.

Rôle6 immédiat : préflightuniqued'inventaire997 etoriginals avantnouvellemath, avecsnapshotpréexec/log/commande/exit. Ownershipround18/conservation*.py/json etrole6/** pourpréflight ; ensuitebancnouveauN1e8 seulementquandle rootautorise unnouveaucandidat. PythonstrictFractions/logintervals signés, jamaisflottant, tousvertices/axesincidencesducontrat,défautsT_A/T_S/parentsmultiplesconservés. Unseulrejeu isolé aprèsPASS, sources/outputsfigés ; aucunoldm/PASS/kernel/sign/copie/PDF/Leanrerun. Annexe18 éventuelle distincte sansmuter17.

Notations : u=logN,ell=logu,alpha=ceilN1/4,Q=floor((N-1)/alpha),a=ceilN7/16,M=ceilN3/4. Sourceonsetu>=10^24, jamais1024 ; N1e8 n'évaluepasceonset. W_kernel et -W_kernel demeurentdistincts ; Ddivisoriel n'estpasD_N. FirstaxisrawΛ_Nsansμ(n)^2. FixedledgerD_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0), Iglobalacquis. originalQ/k1/wholeU_a, vraisS(bN), e1/c1/b1, principal-S(N)N, faces/nonbulk/cofacteurslongs, P5K2/J2surblocentieravantretraits, coûtschacununefois. Leslabelsanalysesnemultiplientpaslesressourcesphysiques.

Sources mathlib/Leanconnuesetlecture : Lean4.15.0commit11651562caae, exesha8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08 ; mathlibq356commit9837ca9d65d9de6fad1ef4381750ca688774e608. Cache8libs déjàprésent, aucuninstall. Pourclaims techniquesniches/sourcesnouvelles, vérificationprimairewebobligatoire ; aucune autorisation externe ou messageriehumain nécessaire. Rechercheautonome continue, pas de limite de cycles utilisateur.
'''
(R/'PROBE_BLOCK.md').write_text(probe,encoding='utf-8')
obs=dict(status='ROUND18_FRESH_CONSTRAINTS_INTAKE_PREPARED',strict_artifacts_exit=0,report_helper_exit=0,findings31=True,pruned5=True,max_depth=2,
         protected997=True,registry_sha256=h(R/'previous_artifacts_sha256.json'),probe_sha256=h(R/'PROBE_BLOCK.md'),nodes_selected=False,
         numeric_or_Lean_started=False,ideation_dispatch_pending=True,victory=False)
(C/'messages/round18_intake.json').write_text(json.dumps(obs,indent=2)+'\n',encoding='utf-8')
p=C/'checkpoint.json';cp=read(p)
cp['phase']='ROUND18_FRESH_CONSTRAINTS_AND_PROBE_READY'
cp['next_protected_registry_pending']='round18/previous_artifacts_sha256.json'
cp['last_progress']+=' Feedback17 saved, helperreport regenerated and strictartifactscheck exit0OK afteractualdone nodes13.9/14.2; freshconstraints31findings5pruned read. Exactinherited997 registry and PROBE18 saved, no18node/bank/Lean selected/launched. Next two quantitativeideations and uniqueconservationpreflight todispatch; goalactive/noWin.'
cp['previous_goal_turn_evidence']+=['round18/PROBE_BLOCK.md','round18/previous_artifacts_sha256.json','.arbor/sessions/parity/.coordinator/messages/round18_intake.json']
p.write_text(json.dumps(cp,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(obs))
