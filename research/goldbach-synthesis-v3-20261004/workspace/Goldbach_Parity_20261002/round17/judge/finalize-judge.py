"""Read-only closure of successful remaining stages; never rerun audit/Lean/banks."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re
from datetime import datetime,timezone
HERE=Path(__file__).resolve().parent;ROUND=HERE.parent
def h(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):d.update(b)
 return d.hexdigest()
def load(n):return json.loads((HERE/n).read_text(encoding='utf-8'))
def save(n,d):(HERE/n).write_text(json.dumps(d,indent=2,sort_keys=True)+'\n',encoding='utf-8')
assert not (HERE/'final_receipt.json').exists(),'Judge closure already frozen'
a=load('audit_receipt.json');first=load('launch_receipt.json');second=load('continuation_receipt.json');last=load('continuation02_receipt.json')
assert first['exit_code']==second['exit_code']==1 and last['exit_code']==0
assert a['independent_audit_attempts']==3 and a['first_failure_technical_guard_only'] and a['continuation01_exit1_technical_nullable_reference']
assert a['new_counts']=={'modules':5,'theorems':93,'defs':40,'instances':1,'axioms_printed':134}
assert a['cumulative_counts']=={'modules':22,'theorems':337}
assert a['score']==0 and a['victory'] is False and a['whole_D_N_uncontrolled']
assert a['preservation_before']['files']==a['preservation_after']['files']==799
assert a['rational_signs']==390 and a['rational_sign_distribution']=={'POSITIVE':242,'NEGATIVE':62,'ZERO':86}
assert a['distinct_C4_rational_signs']==64 and a['distinct_C4_sign_distribution']=={'POSITIVE':54,'NEGATIVE':10}
for receipt,source,snapshot,log in [(first,'run-audit.py','audit_source.py.txt','audit.log'),(second,'continue-audit.py','continuation_source.py.txt','continuation.log'),(last,'continue-audit02.py','continuation02_source.py.txt','continuation02.log')]:
 assert receipt['source_sha256']==receipt['snapshot_sha256']==h(HERE/source)==h(HERE/snapshot)
 assert receipt['log_sha256']==h(HERE/log)
modules=a['independent_new_compiles'];allowed={'propext','Classical.choice','Quot.sound'}
for m in modules:
 assert m['exit_code']==0 and h(Path(m['source_original']))==h(Path(m['source']))==m['source_sha256']==h(Path(m['snapshot']))
 assert h(Path(m['output']))==m['olean_sha256'] and h(Path(m['log']))==m['log_sha256']
 for axes in m['axioms'].values():assert set(axes)<=allowed
 assert 'error:' not in Path(m['log']).read_text() and 'warning:' not in Path(m['log']).read_text()
inputmap={'status':'READ_ONLY_INPUT_AND_RESULT_MAP','input_manifest':str(HERE/'input_sha256.json'),'input_manifest_sha256':h(HERE/'input_sha256.json'),
 'author_inputs143':a['input_sha256'],'originals_and_fixed_contexts':load('input_sha256.json'),
 'modules_in_real_import_order':modules,'initial_numeric_positions390':a['rational_sign_distribution'],
 'distinct_C4_positions64':a['distinct_C4_sign_distribution'],'prior799':a['preservation_after'],
 'audit_attempts':[first,second,last],'parity_bypass_proved':False,'whole_D_N_bound_proved':False,'score':0,'victory':False}
save('input_map.json',inputmap)
rows='\n'.join('| '+m['module']+' | '+str(m['theorems'])+' | '+str(m['defs'])+' | '+str(m['instances'])+' | '+str(m['axioms_printed'])+' | 0 |' for m in modules)
hashrows='\n'.join('* `'+m['module']+'` : source `'+m['source_sha256']+'`, olean neuf `'+m['olean_sha256']+'`, log `'+m['log_sha256']+'`.' for m in modules)
report=f'''# Boucle 17 — Juge indépendant FINAL

Verdict : **acquis partiels vérifiés ; score 0, victory=false**. Les cinq nouveaux modules Lean compilent fraîchement, sans erreur, warning, `sorry`, `admit`, axiome ajouté ni `native_decide`. Ils donnent 93 théorèmes auxiliaires, 40 définitions et une instance. Le résultat sur G est une minoration réelle dérivée sous un input analytique indépendant visible. Le paiement du résidu entier D_N et un contournement effectif de la parité restent absents ; le succès du compilateur sur ces acquis ne satisfait donc pas la condition de victoire.

## Sources gelées et indépendance

Tous les FINAL des rôles 1, 2, 3, 4 et 6, l’addendum des masques et l’annexe C4 séparée ont été reçus avant le gel. `judge/input_sha256.json` lie 143 fichiers de round17, les deux originaux PDF/ZIP, les contextes fixes et l’exécutable Lean ; SHA `{h(HERE/'input_sha256.json')}`. Les 799 archives précédentes (701 + 98), leur inventaire exact et les originaux sont conservés avant et après. Aucun fichier auteur n’a été modifié par le Juge. Aucun ancien producteur, banque PASS, W, olean, dépendance ou PDF n’a été relancé. Le A7 canonique acquis16 demeure inchangé.

Le Juge n’a importé ni exécuté le Python des producteurs. Il a lu les deux banques initiales et les copies isolées existantes, les 33 bindings initiaux, puis les 15 bindings de l’annexe et son rapport distinct. Les certificats de signes sont lus avec leurs bornes rationnelles strictes ; leurs logarithmes et signes ne sont pas recalculés. Les 47 W stockés demeurent des primitives immuables. Le contrôle indépendant des supports, factorizations, racines, CRT, poids, masques et recettes exactes n’est pas un replay de banque.

## Compilations fraîches réellement exécutées

Lean 4.15.0, exécutable SHA `8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08`, mathlib commit `9837ca9d65d9de6fad1ef4381750ca688774e608`. Le LEAN_PATH ne contient que `judge/build` et les huit bibliothèques de cache en lecture. Les sources sont copiées dans le build isolé. Les imports nouveaux utilisent les oleans fraîchement produits par le Juge, dans cet ordre réel.

| Module neuf | Théorèmes | Définitions | Instances | Axiomes imprimés | Exit |
| --- | ---: | ---: | ---: | ---: | ---: |
{rows}
| Total | 93 | 40 | 1 | 134 | 0 |

Les 134 déclarations ont chacune un `#print axioms`. Les deux sorties Lean « depends on axioms » et « does not depend on any axioms » sont traitées. Tous les ensembles d’axiomes sont inclus dans `propext`, `Classical.choice`, `Quot.sound` ; aucun axiome personnalisé ni `sorryAx`. Les cinq logs finaux sont propres. Les définitions, instances et dépendances ne sont pas comptées comme théorèmes. Le cumul historique devient 22 modules et 337 théorèmes auxiliaires (17/244 acquis + 5/93 nouveaux).

{hashrows}

## Contenu mathématique effectivement certifié

`FourFormRoots` définit les racines du véritable produit de quatre formes, sa densité, le discriminant de collision et la saturation. Il prouve les bornes locales et la valeur rho=4 hors collision, ainsi que l’annulation de la cellule rough en cas de saturation.

`SelbergFourForms` construit les poids par inversion sur le véritable support carré libre tronqué et par la fonction de Möbius mathlib. Il dérive lambda(1)=1, le support, la norme, la diagonale et le principal 1/G. La minoration ponctuelle par le carré et la majoration finie de la cellule rough gardent la vraie erreur de comptage visible. L’alternative saturation/cellule vide ou non-saturation/construction est prouvée sans demander une borne cible pour G, une valeur rho supposée égale à quatre partout ou une disponibilité de partenaire.

`PowersetMoment` garde la queue entière prod>z et prouve son contrôle par le moment. `FourFormTruncation` relie ce moment au véritable G de Selberg. `FourFormCollisionLoss` dérive

`G_actual(N,e,p0,z) ≥ P(y)^4 * L_Delta(N,e,p0,y) / 2`,

où P(y) est le vrai produit des inverses de 1−1/p et L_Delta le produit des cubes de 1−1/p sur les vrais premiers divisant Delta. L’input analytique visible est `sum_{{p≤y}} log(p)/p ≤ 2+2log(y)`, avec les gardes y≤z, log(z)≥32 et 32log(y)≤log(z), la coprimalité et la non-saturation. Cet input porte seulement sur les premiers jusqu’à y ; il n’est ni G cible ni une prémisse équivalente à la conclusion. La moitié du produit n’est pas introduite comme hypothèse.

Ces modules certifient un crible de Selberg fini, sa troncature et une perte locale de collision. Ils ne certifient pas encore les estimations de Mertens/totient qui convertiraient le produit en la constante C4 du contrat, le CRT+1 uniforme dans Lean, C6, ni un paiement des cellules A/S. Le mode chi13 écrit par le rôle1 traite un couple de coefficients sur le vrai j=v*w ; la disponibilité uniforme de BV et de ses seuils pour tout le Type II, ainsi que Gamma39, restent à payer.

## Numérique fini et portée

Le rough couvre 201 entiers q, 9 premiers unitaires, 28 cœurs et 252 candidats physiques uniques. Les 47 noyaux conservés et 205 références nulles restent distincts : kernel_ref est une chaîne sur47 et null sur205 ; C_recipe est un dictionnaire sur47 et absent sur205. Le drapeau d’exclusion vaut True sur37 et False sur215 selon sa garde réelle. Partition des demandes actives : A=11, R=0, S=18 ; le déficit positif n’est pas payé par la seule cellule R. Les 26 systèmes de racines sont contrôlés effectivement : 10 saturations, 16 non-saturés et 17 488 lignes CRT. Les vrais supports, G, poids, inversion, sommes de carrés et erreurs finies ont leurs identités exactes vérifiées ; aucun rho=4 universel n’est substitué.

Le Type II couvre 162 338 entiers, les colonnes complètes de facteurs, beta=181, theta=12 460, les 8 puissances propres et les six masques hN/77hN. Les caps physiques de s/q sont gardées séparément des caps source. Les produits j=v*w utilisent v=17/19 ; les 503 doubles de 323 gardent leur multiplicité bilinéaire sans créer une capacité physique. Les prix theta, II et II_raw et les classes de chi13 sont distincts. Les erreurs AP/BV demeurent visibles.

Les 390 positions initiales ont 242 POS, 62 NEG et 86 ZERO, avec bornes strictes, sans flottant ni irrésolu. L’annexe C4 a 64 nouvelles positions séparées : 54 POS et 10 NEG. Ses seize cœurs, seize sous-ensembles par cœur, tête et queue (produits105 et210) vérifient Z=sum W=prod(1+h), coeff_logp=Z*g(p), G_P+Tail=Z et G_P≤G_actual(100). Les 6 conditions de demi-moment vraies et les 10 fausses sont conservées. Les 16 marges de Markov sont positives ; G_P≥Z/2 est observé même pour les dix conditions suffisantes fausses. Ces dix résultats ne réfutent pas la conclusion. Le total454 positions ne compte aucun théorème.

N=10^8 est un domaine fini de test. Aucune borne source C4/C6/C7/U4 ou BV n’y est appliquée ; le seuil analytique u≥10^24 n’est pas évalué ou réfuté par ce tableau. Les trois falsifiers initiaux portent sur les promotions locales indiquées dans la banque, pas sur les acquis globaux.

## Erreurs réelles et reprises limitées

Les auteurs ont effectué 30 compilations réelles : 14 par3 et16 par4. Les 23 exit1 (12 + 11), leurs sources/snapshots/logs, sont archivés dans `judge/author_failures.json`. Les diagnostics concernent APIs Lean/mathlib, casts, ensembles finis, simplifications, réécritures dépendantes et élaboration ; aucun blocage analytique de parité n’est inventé à partir de ces erreurs. Les PASS11/14 du rôle3 et PASS8/11/13/15/16 du rôle4 restent distincts. PASS15 a un warning de style conservé, corrigé dans FINAL16 ; ce warning n’est pas un exit1.

Le seul échec numérique auteur initial est technique : la factorisation de rad(hN) sortait du domaine borné du helper. Il est conservé et la correction prend l’union des facteurs des composants bornés. L’annexe C4 a un producteur et un replay exit0, sans échec.

Le Juge a un incident de préparation Windows206 avant création du processus, puis **trois invocations d’audit documentées : exit1, exit1, exit0**. Première erreur pré-Lean : mon audit imposait inconditionnellement `small_factor_exclusion_verified`, alors que le drapeau vaut vrai exactement sous la garde witness et e modulo ell égale witness.j modulo ell. Deuxième erreur pré-Lean : je testais la présence de `kernel_ref`, alors que les205 axes inactifs gardent `kernel_ref:null`. Les corrections vérifient la garde réelle et la référence non nulle. Ce sont deux erreurs techniques du Juge ; aucune identité fausse ni erreur Lean. Tous les premiers sources/snapshots/logs/reçus et marqueurs exclusifs sont conservés. Les étapes PASS de conservation, bindings/copies et signes ont été chargées depuis la première tentative, pas rejouées. La continuation02 exécute seulement le stade candidat inachevé et les étapes restantes, puis les cinq compilations neuves, chacune une fois. Chaque lanceur est gardé contre un rerun par un marqueur O_EXCL.

Reçu première tentative `{h(HERE/'launch_receipt.json')}` ; reçu continuation01 `{h(HERE/'continuation_receipt.json')}` ; reçu continuation02 exit0 `{h(HERE/'continuation02_receipt.json')}`. Audit mathématique et compilations : `judge/audit_receipt.json` SHA `{h(HERE/'audit_receipt.json')}`. Carte d’inputs : `judge/input_map.json` SHA `{h(HERE/'input_map.json')}`. Le finalizer ne compile ni ne teste aucune banque ; il lit et lie les résultats effectifs.

## Obligations laissées ouvertes

Le contrat C4 complet, C6, T_A/T_S, la capacité d’incidence globale, toutes les autres faces du ledger, le Type II entier et Gamma39 ne sont pas payés par ces résultats. Le ledger entier (whole U_a, raw Lambda_N, vrais S(bN), frontières k1/c1/b1, prime powers, annulus et erreur positive) n’est pas remplacé par le petit support. Aucune disponibilité de partenaire n’est ajoutée. La borne whole D_N≤N/(256logNloglogN) et le contournement de parité sont non certifiés. Ces obligations fondent le verdict partiel et la poursuite de la recherche, sans remettre en cause les acquis.
'''
(ROUND/'agent5.md').write_text(report,encoding='utf-8')
assets={}
for p in sorted(HERE.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts and p.name not in ('final_receipt.json','manifest.json'):assets[p.relative_to(HERE).as_posix()]=h(p)
final={'status':'FINAL_ROUND17_INDEPENDENT_JUDGE_PARTIAL','timestamp_utc':datetime.now(timezone.utc).isoformat(),'report':str(ROUND/'agent5.md'),'report_sha256':h(ROUND/'agent5.md'),
 'input_manifest_sha256':h(HERE/'input_sha256.json'),'audit_receipt_sha256':h(HERE/'audit_receipt.json'),'input_map_sha256':h(HERE/'input_map.json'),
 'initial_audit_exit_code':1,'continuation01_exit_code':1,'continuation02_exit_code':0,'independent_audit_invocations':3,'real_Judge_technical_pre_Lean_failures':2,
 'pre_launch_Windows206_process_created':False,'new_fresh_Lean_invocations':5,'new_fresh_Lean_exit_zero':5,'new_fresh_Lean_exit_nonzero':0,
 'new_counts':a['new_counts'],'cumulative_counts':a['cumulative_counts'],'producer_Lean_invocations':30,'producer_Lean_failures23':23,
 'initial_positions390':a['rational_sign_distribution'],'distinct_C4_positions64':a['distinct_C4_sign_distribution'],
 'preservation799':a['preservation_after'],'own_assets_sha256':assets,'own_asset_count_before_final_receipt':len(assets),
 'old_PASS_or_bank_reexecuted':False,'W_or_sign_recomputed':False,'old_Lean_or_dependencies_compiled':False,'author_files_changed':False,
 'availability_assumed':False,'C4_full_C6_A_S_global_TypeII_Gamma_unproved':True,'whole_D_N_bound_proved':False,'parity_bypass_proved':False,'score':0,'victory':False}
save('final_receipt.json',final);assets['final_receipt.json']=h(HERE/'final_receipt.json')
save('manifest.json',{'status':'FINAL_FROZEN_JUDGE17_PARTIAL','sha256_relative_judge':assets,'files':len(assets),'report_relative_round17':'agent5.md','report_sha256':h(ROUND/'agent5.md'),
 'receipt_sha256':assets['final_receipt.json'],'input_manifest_sha256':h(HERE/'input_sha256.json'),'author_inputs143_unchanged':True,
 'audit_invocations3_exit_codes':[1,1,0],'new_Lean_modules5_theorems93_defs40_instance1':True,'protected_previous':799,'score':0,'victory':False})
print(json.dumps({'report_sha256':h(ROUND/'agent5.md'),'receipt_sha256':h(HERE/'final_receipt.json'),'manifest_sha256':h(HERE/'manifest.json'),
 'audit_receipt_sha256':h(HERE/'audit_receipt.json'),'bindings':len(assets),'victory':False}),flush=True)
