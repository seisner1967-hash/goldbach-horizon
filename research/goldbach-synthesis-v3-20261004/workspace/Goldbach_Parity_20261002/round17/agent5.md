# Boucle 17 — Juge indépendant FINAL

Verdict : **acquis partiels vérifiés ; score 0, victory=false**. Les cinq nouveaux modules Lean compilent fraîchement, sans erreur, warning, `sorry`, `admit`, axiome ajouté ni `native_decide`. Ils donnent 93 théorèmes auxiliaires, 40 définitions et une instance. Le résultat sur G est une minoration réelle dérivée sous un input analytique indépendant visible. Le paiement du résidu entier D_N et un contournement effectif de la parité restent absents ; le succès du compilateur sur ces acquis ne satisfait donc pas la condition de victoire.

## Sources gelées et indépendance

Tous les FINAL des rôles 1, 2, 3, 4 et 6, l’addendum des masques et l’annexe C4 séparée ont été reçus avant le gel. `judge/input_sha256.json` lie 143 fichiers de round17, les deux originaux PDF/ZIP, les contextes fixes et l’exécutable Lean ; SHA `40076625c36a04c5cef48ece8ee2d4fe625715cfbe1bf06364ae3da5b182bcb1`. Les 799 archives précédentes (701 + 98), leur inventaire exact et les originaux sont conservés avant et après. Aucun fichier auteur n’a été modifié par le Juge. Aucun ancien producteur, banque PASS, W, olean, dépendance ou PDF n’a été relancé. Le A7 canonique acquis16 demeure inchangé.

Le Juge n’a importé ni exécuté le Python des producteurs. Il a lu les deux banques initiales et les copies isolées existantes, les 33 bindings initiaux, puis les 15 bindings de l’annexe et son rapport distinct. Les certificats de signes sont lus avec leurs bornes rationnelles strictes ; leurs logarithmes et signes ne sont pas recalculés. Les 47 W stockés demeurent des primitives immuables. Le contrôle indépendant des supports, factorizations, racines, CRT, poids, masques et recettes exactes n’est pas un replay de banque.

## Compilations fraîches réellement exécutées

Lean 4.15.0, exécutable SHA `8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08`, mathlib commit `9837ca9d65d9de6fad1ef4381750ca688774e608`. Le LEAN_PATH ne contient que `judge/build` et les huit bibliothèques de cache en lecture. Les sources sont copiées dans le build isolé. Les imports nouveaux utilisent les oleans fraîchement produits par le Juge, dans cet ordre réel.

| Module neuf | Théorèmes | Définitions | Instances | Axiomes imprimés | Exit |
| --- | ---: | ---: | ---: | ---: | ---: |
| FourFormRoots | 33 | 10 | 1 | 44 | 0 |
| PowersetMoment | 5 | 2 | 0 | 7 | 0 |
| SelbergFourForms | 42 | 23 | 0 | 65 | 0 |
| FourFormTruncation | 8 | 2 | 0 | 10 | 0 |
| FourFormCollisionLoss | 5 | 3 | 0 | 8 | 0 |
| Total | 93 | 40 | 1 | 134 | 0 |

Les 134 déclarations ont chacune un `#print axioms`. Les deux sorties Lean « depends on axioms » et « does not depend on any axioms » sont traitées. Tous les ensembles d’axiomes sont inclus dans `propext`, `Classical.choice`, `Quot.sound` ; aucun axiome personnalisé ni `sorryAx`. Les cinq logs finaux sont propres. Les définitions, instances et dépendances ne sont pas comptées comme théorèmes. Le cumul historique devient 22 modules et 337 théorèmes auxiliaires (17/244 acquis + 5/93 nouveaux).

* `FourFormRoots` : source `49cbf93fd8eb9aa75236419d5d7b95e1841d67571865171115ffbbdfcb71e9fa`, olean neuf `4a13fc20feabfd5ff552f5dbd18c99c6b66bcfe1a65a3f44fff555417d7b4021`, log `3b943e6e6ea23b1baef7ea519b64ffedf9655c60912947e3a3b2f4ad4af99edd`.
* `PowersetMoment` : source `971f351decef7e78112ec940c5ee553806abecccaf19440a4d661881c4ae188d`, olean neuf `f1b9c19267d9c6df430156f3731613bd1fbcf58bf50e626417a74dc8449f1905`, log `c30608116846aa2c3cfe25a94fdb865d3decd8859af08c083e77c8692db911b1`.
* `SelbergFourForms` : source `b1b658aa92f8e02cef29667e9e60b763ca3ef57bb25dcbc8aa9c50ba33591ce1`, olean neuf `9639c1f7ae9eb03d07c1de2fd79cdea4dd503d29716e5de3adb4085de21fc46c`, log `772f8de4075a4d31edbdcedb6544f236745e4e066388cf616abc69b613e539b1`.
* `FourFormTruncation` : source `577ff585207e72bf5d31121743fc218effc91eb8a460cef9fa9ee2e05a3996e0`, olean neuf `340667c515537e2d5501e19329c4becb39cef6989699439107f85a4ec520dbc1`, log `fb1c9d7c230bd3f9e0d9516bd4c09d84b9a8028e10244f622991b63c24d852ca`.
* `FourFormCollisionLoss` : source `000cade7cac3a1c9472a2fd465e992de71a49c6ad65ae85635726d196392d9a5`, olean neuf `e8f5c07ef6225671165e1fb942d4f0c39e3540ee8d1a3ee1e21d0205e10a3091`, log `16f84da8a2c1e9dbeb01d22812823ff575666f31fb358341208b7949bf3907ac`.

## Contenu mathématique effectivement certifié

`FourFormRoots` définit les racines du véritable produit de quatre formes, sa densité, le discriminant de collision et la saturation. Il prouve les bornes locales et la valeur rho=4 hors collision, ainsi que l’annulation de la cellule rough en cas de saturation.

`SelbergFourForms` construit les poids par inversion sur le véritable support carré libre tronqué et par la fonction de Möbius mathlib. Il dérive lambda(1)=1, le support, la norme, la diagonale et le principal 1/G. La minoration ponctuelle par le carré et la majoration finie de la cellule rough gardent la vraie erreur de comptage visible. L’alternative saturation/cellule vide ou non-saturation/construction est prouvée sans demander une borne cible pour G, une valeur rho supposée égale à quatre partout ou une disponibilité de partenaire.

`PowersetMoment` garde la queue entière prod>z et prouve son contrôle par le moment. `FourFormTruncation` relie ce moment au véritable G de Selberg. `FourFormCollisionLoss` dérive

`G_actual(N,e,p0,z) ≥ P(y)^4 * L_Delta(N,e,p0,y) / 2`,

où P(y) est le vrai produit des inverses de 1−1/p et L_Delta le produit des cubes de 1−1/p sur les vrais premiers divisant Delta. L’input analytique visible est `sum_{p≤y} log(p)/p ≤ 2+2log(y)`, avec les gardes y≤z, log(z)≥32 et 32log(y)≤log(z), la coprimalité et la non-saturation. Cet input porte seulement sur les premiers jusqu’à y ; il n’est ni G cible ni une prémisse équivalente à la conclusion. La moitié du produit n’est pas introduite comme hypothèse.

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

Reçu première tentative `1750dbfeef59c99342078f505dc66bb777abf389ae64e12ec4172db498808863` ; reçu continuation01 `abf29025da507ea24884401adc5c32aade22797de0b7147111ae6af3d72ef155` ; reçu continuation02 exit0 `db7573e6bb22fcb637a7723e9c6f18df6f321fcca7448446848f41c8e0a9dfb3`. Audit mathématique et compilations : `judge/audit_receipt.json` SHA `f44584f6a6a39679ad61108fe2d660d05f64769301a9f7c8f71b0227f008117e`. Carte d’inputs : `judge/input_map.json` SHA `25965e53b1efb5fc2c339fee4e79e5d207787f353d5864d7e87fc6541bd9a1d7`. Le finalizer ne compile ni ne teste aucune banque ; il lit et lie les résultats effectifs.

## Obligations laissées ouvertes

Le contrat C4 complet, C6, T_A/T_S, la capacité d’incidence globale, toutes les autres faces du ledger, le Type II entier et Gamma39 ne sont pas payés par ces résultats. Le ledger entier (whole U_a, raw Lambda_N, vrais S(bN), frontières k1/c1/b1, prime powers, annulus et erreur positive) n’est pas remplacé par le petit support. Aucune disponibilité de partenaire n’est ajoutée. La borne whole D_N≤N/(256logNloglogN) et le contournement de parité sont non certifiés. Ces obligations fondent le verdict partiel et la poursuite de la recherche, sans remettre en cause les acquis.
