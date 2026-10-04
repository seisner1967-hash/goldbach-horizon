# Goldbach — point de recherche du 3 octobre 2026

**Verdict du Juge : aucune victoire établie.** Les six rôles ont été exécutés par vagues au cours de vingt boucles, en utilisant le cache mathlib local. Cinquante-sept fichiers Lean ont été compilés puis reconstruits indépendamment, avec942 conclusions auxiliaires distinctes et uniquement les axiomes classiques autorisés. La boucle18 ajoute huit modules et170 théorèmes sur les incidences TypeII, leurs prix, les fronts CRT et les formes divisées du switch SS, avec les hypothèses quantitatives restantes explicites. La boucle17 ajoute cinq modules et93 théorèmes sur le vrai crible fini, la troncature et une perte de collisions ; son minorant de G garde un input analytique indépendant. La boucle16 ajoute deux modules et36 théorèmes : une marge canonique1/144 sur la vraie série singulière est certifiée sous l’enclosure C2 acquise ; l’incidence quantitative reste ouverte. La boucle13 ajoute deux modules et39 théorèmes sur un échange arithmétique réel et sa variation harmonique finie. La boucle14 vérifie les deux déficits des graphes et leurs capacités physiques ; son paiement écrit du front reste limité à une sous-famille. Les boucles14/15 n'appellent aucun Lean supplémentaire faute de candidat quantitatif ;15 conserve une covariance réelle et un sélecteur de cibles sans partenaire. Leur comparaison pondérée entière et le complément restent ouverts. Aucune borne du résidu terminal D_N ni contournement analytique global de la parité n'est établi. Les identités de convolution, de Fourier et de coordonnées et l'interpolation de facteurs ne sont pas présentées comme des nouveautés mathématiques.

Ce rapport est un checkpoint de recherche, pas une preuve de clôture de l'objectif. Les sources antérieures ont été conservées ; les essais et les extensions sont dans ce dossier.

**Boucle22 — pivot continu actif :** sur directive explicite de l'utilisateur, les méthodes bilinéaires, de crible combinatoire, d'inversion de Möbius, de Vaughan et d'estimation scalaire des restes AP sont abandonnées pour la suite. Les travaux21 ont été interrompus avant toute compilation ou exécution mathématique nouvelle ; leurs sources restent archivées sans validation. Les57modules/942conclusions historiques restent les seuls comptes certifiés. La recherche vise maintenant une identité analytique exacte spectrale, modulaire ou opératorielle avec troncature contrôlée à N=10^8 et enveloppe d'erreur fermée, continue, certifiable sous Lean4. Deux propositions papier sont maintenant gelées et sélectionnées : trace réelle premiers–zéros (15.2) et déroulement Epstein du réseau complet (16.1). ROLE3/4 préparent leurs preuves sans compiler ; ROLE6 prépare24cas géométriques, dont6 à y=10000, avec racines à encadrement dyadique96bits et queue fermée positive. Le banc géométrique unique du rôle6 a terminé à06:49:54UTC avec exit0 :24cas compatibles dans la tolérance1/100000,18comparaisons de fenêtres et16mutations du facteurq détectées ;295198certificats carrés sont archivés. Ce résultat est EPSTEIN_UNFOLDING_AUX_PASS. La première invocation Lean22 du noyau réel a échoué à07:02:31UTC avec exit1 : erreurs de simplification et d'élaboration, source et log conservés, aucun olean ni crédit formel. La révision02 du noyau a réellement compilé à07:15:17UTC avec exit0, 28théorèmes et5définitions ; 33sorties axioms standard sont dans le log. C'est un PASS d'auteur auxiliaire, avec contrôle indépendant encore attendu. Le déroulement infini et la queue continue restent en sources, et le bilan globalD_N reste ouvert. Il ne calcule ni le signal de chaleur, ni le coefficientN, ni D_N. L'identification opérateur, les producteurs Gamma/zêta certifiés, le coefficient global à N et le raccord D_N restent ouverts. [Directive](round22/USER_DIRECTIVE.md), [contrat de phase](round22/PROBE_BLOCK.md).

**Boucle20 close :** seize nouveaux modules ont été compilés indépendamment sans sorry,250 théorèmes,83 définitions,1 structure et334 prints d’axiomes standards. L’audit unique a terminé le3octobre à04:52:05UTC avec exit0 et13 warnings bénins. Les22 FAIL techniques des38 invocations auteurs sont conservés. Les six modules composites construisent les vrais poids et l’identité avec queue, slack et restes AP ; les dix modules friables prouvent le coût theta déclaré sur H19∩(F0∨F1) plus les réciproques F1 uniques ≤N/(8192 logN loglogN), sous le seul seuil source logN≥10^24. Les réciproques non friables F0\F1, le complément, le pont au support entier, SD/M0, Gamma/capacités et tout le bilan D_N restent ouverts. Les deux bancs N=10^8 ont un exit0 unique avec gardes source fausses. Cumul57 modules/942 théorèmes auxiliaires ; aucune victoire. [Rapport indépendant](round20/agent5_judge.md), [budget source partiel](round20/role4/FriableSourceBudget.lean), [feedback](round20/ideation_failure_feedback20_final.md), [controller20](round20/controller_manifest.json).

**Boucle19 close :** onze modules compilés indépendamment,185 théorèmes,78 définitions,3 structures et268 prints d'axiomes standards. Audit unique exit0 terminé le3octobre à01:36:25UTC ; zéro reprise du Juge ou replay. Les18 FAIL techniques des29 invocations auteurs et un échec préalable de lanceur sont archivés. Les deux banques neuves N=10^8 ont chacune un PASS unique. Γ_rank peut compenser le prix principal négatif ; AP/K14/K18/BV, support source, medium/long, capacité et bilan entier restent ouverts. Le seuil local écrit10^40 ne paie pas le segment source depuis10^24. Aucune victoire. [Rapport indépendant](round19/agent5.md), [estimateur réel](round19/role3/RankCalibrationEstimator.lean), [switch non-SS réel](round19/role4/NonSSBracketSwitch.lean), [controller19](round19/controller_manifest.json).

## Sources et notations

La monographie fournie compte 51 pages. Son texte est extrait dans `monographie.txt`. Le ZIP fourni contient six fichiers de continuation et de contrôles, et **aucun fichier Lean**. Les certificats cités du sprint 15 ont été retrouvés dans `Goldbach_Research_20260930/sprint15`, dont les définitions réelles de Möbius et les décompositions short/long. Les empreintes des deux fichiers fournis sont dans `INPUT_HASHES.json`.

**Lecture visuelle corrigée en boucle 8 :** l'onset adaptatif de la source est u>=10^24, avec un exposant24, aux pages32 (66),33 et36 (72). L'extraction avait aplati cet exposant en «1024». Les acquis, notamment le paiement global de I, sont utilisés dans leur domaine original. Les anciens reçus restent figés ; toute mention antérieure d'un onset adaptatif u>=1024 est corrigée par cette annotation. Les constantes1024 de budget et les préfixes1024 sont distincts et inchangés. Les rendus de source et leur reçu sont dans round8/SOURCE_ONSET_CLARIFICATION.md.
Le profil de la cible est alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), u=log N et ell=log u. Le profil en N^(1/8) reste séparé. À N=100000000, alpha=100 et Q=999999. Le noyau divisoriel D_{alpha,Q}(m) est distinct du résidu D_N. Après le pont couvert exact, la monographie donne

    D_N = -Sfull + 2 max(e,0).

Il reste donc à prouver un contrôle de l'agrégat signé complet. Déduire la cible en supposant directement sa reformulation sur Sfull ne serait pas une victoire.

## Résultats Lean effectivement reçus

| Fichier | Conclusions auditées | Contenu exact | Limite pertinente |
| --- | ---: | --- | --- |
| `lean/ParityWeights.lean` | 19 | Projecteurs (mu²±mu)/2, identités bilinéaires sur facteurs coprimes, réponses prime/semiprime/triprime, contre-réponse concrète rugueuse | Le projecteur impair conserve les triprimes |
| `lean/QuarticMobius.lean` | 11 | Inversion quartique, reste nul avant (alpha+1)^4, insertion sur la frontière avec coefficient réel sur un tuple arbitraire | La combinaison additive -6,+4,-1 n'est pas estimée |
| `lean/ChenWeight.lean` | 8 | Nombre de facteurs avec multiplicité, preuve de Omega≤3 par rugosité, détecteur quadratique exact et insertion réelle | La rugosité complète n'est pas fournie par r>alpha ; le moment du poids n'est pas estimé |

Les produits de fonctions arithmétiques dans la formule suivante sont des convolutions de Dirichlet. Pour M=mu·1_{n≤alpha} et L=mu-M,

    mu = 4M - 6M²*zeta + 4M³*zeta² - M⁴*zeta³ + L⁴*zeta³.

Le dernier terme est nul pour n<(alpha+1)^4. Pour alpha<r<N≤alpha^4,

    mu(r) = -6(M²*zeta)(r) + 4(M³*zeta²)(r) - (M⁴*zeta³)(r).

L'insertion réelle conserve le coefficient du tuple complet. Elle ne réduit pas le module CRT original ar à un produit de seuls facteurs courts.

Pour 1<m<(alpha+1)^4, si **tous** les premiers divisant m dépassent alpha, le nombre Omega de facteurs premiers, avec multiplicité, vérifie 1≤Omega≤3. Alors

    W(m) = (Omega(m)-2)(Omega(m)-3)/2 = 1_{m premier}.

Cette égalité ne suppose pas la primalité ni la carré-liberté. Elle utilise un compte exact de facteurs, dont la distribution additive n'a pas été contrôlée. Appliquer W à un cofacteur r détecte r premier ; cela ne détecte pas m=kr premier lorsque k>1. Sur le support carré-libre, sa forme quadratique peut s'écrire à partir des incidences de diviseurs premiers. Hors de ce support, les paires d'occurrences peuvent avoir la même valeur première et doivent être conservées.

## Juge indépendant et reproduction

Lean 4.15.0, commit 11651562caae ; cache mathlib au commit 9837ca9d65d9de6fad1ef4381750ca688774e608. Le Juge a reconstruit GoldbachBridge, GoldbachArithmetic et GoldbachMoebiusShortLong depuis leurs sources dans `judge/dependencies`. Les nouveaux fichiers sont compilés dans `judge/output`. Aucun ancien olean Goldbach n'est utilisé pour le rejeu des nouvelles conclusions.

Les six modules sortent avec code 0. Les 38 conclusions nouvelles et 40 conclusions de dépendances imprimées, soit 78 déclarations auditées, ne dépendent que de propext, Classical.choice et Quot.sound. Le reçu `judge_receipt.json` contient les empreintes du compilateur, des sources, des logs, des oleans et des filtres numériques. Le scanner de code écarte les preuves incomplètes, les nouvelles déclarations d'axiomes et la décision native. Le drapeau de victoire faux dans le reçu décrit le verdict sémantique de ces fichiers ; il n'est pas une règle affirmant que toute compilation réussie est une percée analytique.

Rejeu PowerShell hors ligne, depuis ce dossier :

```powershell
& .\build-judge.ps1 -NewModules @('ParityWeights','QuarticMobius','ChenWeight') -ExtraDependencies @('GoldbachMoebiusShortLong')
```

Les paramètres du script permettent d'indiquer les chemins locaux du compilateur, du cache et des sources de dépendances. Aucun paquet n'a été installé et aucun acquis n'a été modifié.

## Filtres numériques exacts

`numerical/parity_checks.py` : PASS, code 0, 1 767 478 cas comptabilisés. Tous les 535 693 triprimes 100<p<q<r et pqr<10^8 ont été énumérés. Le candidat impair corrigé par les triprimes et le poids quadratique initial ont chacun passé 539 648 contrôles ; l'identité quartique a passé 18 866 contrôles sans reste et 12 001 avec reste. Les 4 096 faces additives choisies par formule déterministe sont un échantillon déclaré, pas toutes les faces de N.

`numerical/chen_multiplicity_checks.py` : filtre préalable PASS, 24 121 cas. `numerical/round2_checks.py` : contrôle indépendant PASS, 24 371 appels du poids. Les classes répétées sont exhaustives : 1 204 carrés p², 65 cubes p³ et 21 648 produits p²q avec p≠q, tous leurs premiers >100 et produit<10^8. Les coefficients logarithmiques du diagnostic local sont des rationnels exacts sur des logarithmes symboliques. Aucune comparaison de flottants ne remplace une identité arithmétique.

Reproduction du premier banc :

```powershell
& 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe' .\numerical\parity_checks.py
```

Les autres bancs s'exécutent avec le même interpréteur. Les anciens scripts et reçus ont été vérifiés inchangés par le second banc. Ces contrôles n'établissent aucune estimation asymptotique et ne calculent pas D_N.

## Échecs et corrections conservés

| Journal | Échec exact | Réparation et classement |
| --- | --- | --- |
| `agent3_parity_compile01.log` | Tactique arithmétique sans borne suffisante sur le produit des trois premiers | Chaîne explicite d'inégalités ; erreur technique |
| `agent3_parity_compile02.log` | Borne 1≤r manquante à la tactique et facteur p*q*1 non simplifié | Hypothèse fournie et simplification ; erreur technique |
| `agent4_quartic_compile01.log` | Tactique après but déjà résolu, constante sub_apply inexistante, exposant de monotonie absent | Suppression de l'étape superflue, change et exposant explicite ; erreurs techniques |
| `agent4_quartic_compile02.log` | Numéraux de l'anneau des fonctions non normalisés par le lemme de conversion | Lemmes explicites pour 4 et 6 ; erreur technique |
| `agent4_chen_compile01.log` | Réécriture de n modifiant aussi n dans l'indice de la liste de ses facteurs | Calcul en deux étapes conservant l'indice ; erreur technique |

Ces cinq tentatives sont des échecs de compilation. Les traces de preuve incomplète imprimées par Lean sur leurs buts échoués ne sont jamais acceptées comme preuve. Les versions finales et le rejeu frais les éliminent. Une erreur de tactique n'est pas un diagnostic automatique du mur de la parité.

Les échecs mathématiques, filtrés séparément, sont précis :

- Le projecteur impair seul laisse m=101*103*107=1113121 : il vaut un alors que Lambda(m)=0. La contribution triprime ne peut pas être omise.
- À N=10^8, a=21, b=13, r=99999727=7951*12577, k=1, y=W=2 donne P=4,Q=0 et r>100, avec module CRT ar=2099994267. L'annulation interne automatique est fausse ; une compensation globale n'est pas réfutée.
- Supprimer le reste quartique hors domaine échoue à alpha=2,n=81 : polynôme=-1, mu=0 et reste=1. L'analogue 101^4 dépasse N=10^8.
- Remplacer la rugosité complète de m par celle d'un seul cofacteur échoue pour m=3*101*103*107 : Omega=4, W=1 et m composé dans la fenêtre.
- Pour N=10^8, m=303 et n=99999697=7*41*348431, le noyau exact satisfait D(303)-W(n,303)=log(101)/2>0. Comme fII(n)=-log n et mu(m)=1, ce terme contribue négativement à Sfull. Son partenaire m=101 a un noyau nul. Le poids harmonique laisse un commutateur non nul ; une fermeture favorable terme par terme est donc fausse. Aucun no-go global n'est déduit de ce cas.

La dernière identité orbitale et son diagnostic sont détaillés dans `agent1_round2.md` et contrôlés dans `numerical/round2.json`.

## Boucle 3 certifiée : direction spectrale et blocs complets

Les deux rôles d'idéation ont rendu `round3/agent1_multifibre.md` et `round3/agent2_projection.md`. Le premier conserve le poids Lambda(N-m)-log(N-m) à chacune des fibres déplacées. Le bloc complet m=101,303,707,2121, à N=10^8, est défavorable sans extrémité géométrique : les deux termes centraux sont strictement négatifs, les deux autres nuls. La conclusion locale favorable est écartée avant compilation. Ce constat ne réfute aucune borne globale.

Le second regroupe les coefficients HH signés par eta=-a/(s*t) dans le groupe des unités modulo N. Sur une cellule réellement séparée, la projection multiplicative devient chi(-1) A_chi U_bar(chi) V_bar(chi), et la transformée du Kloosterman devient tau(bar(chi))^2 chi(h*b*l) lorsque h,b,l sont unités. Le reste des masques couplés et les fréquences non unités restent explicites. L'entrée de préfixes mu acquise donne seulement un contrôle de petits conducteurs retenus ; aucun contrôle de la projection haute n'a été établi.

Le filtre `round3/multifibre_checks.py` est passé, code 0 : 3 084 paires réelles admises, dont 1 602 négatives, 1 266 positives et 216 nulles, avec signes certifiés par des intervalles rationnels de logarithmes. Le transport fini conserve ses faces supérieures non nulles. À N=10^8, l'histogramme spectral direct est égal à la convolution sur son support séparé, avec 2 214 résidus non nuls. Ajouter le masque a<s réfute sa factorisation sans reste : -4 contre -2 au résidu 122399. Les diagnostics de Gauss sur les modules 11 et 829 et le tuple N=1658 sont des tests finis séparés, pas le secteur analytique de N=10^8. Les anciens fichiers numériques sont inchangés.

Le Juge a recompilé `round3/lean/MultifibreObstruction.lean` et `round3/lean/QuotientGauss.lean` : respectivement 20 et 11 nouveaux théorèmes, sans erreur, avertissement ou preuve incomplète, avec seulement propext, Classical.choice et Quot.sound. Il a reconstruit depuis leurs sources GoldbachBridge (10 déclarations imprimées), GoldbachArithmetic (15) et ParityWeights (19). Le reçu de cette boucle audite donc 75 déclarations, dont 31 nouvelles. Avec les 38 précédentes, 69 conclusions nouvelles distinctes sont désormais certifiées. Le premier reçu et son builder sont inchangés.

`literalFourSiteBlock_neg` calcule les noyaux D/W aux trois préfixes utiles et les poids Mangoldt aux quatre sites ; aucune valeur de K n'est supposée. Le préfixe est prouvé équivalent à la face stricte alpha*k<m. Les définitions littérales correspondent à la formule de la monographie ; le raccord de noms vers l'ancien module n'est pas un théorème intermodule supplémentaire. La transformation de Gauss est prouvée sur un anneau commutatif fini, puis sur ZMod N composite, avec les contraintes d'unités dans les types. Les variantes conjuguée et réelle conservent ces contraintes. Ce sont des certificats d'identités et d'obstruction locale ; aucune nouveauté analytique ni victoire n'est revendiquée.

Le rejeu numérique indépendant du Juge est également PASS : les champs déterministes des deux JSON de la boucle sont reproduits dans un dossier isolé. Les sources et reçus de production restent inchangés. Le reçu `round3/judge_receipt.json` lie les hashes des sources, des oleans, des logs et des filtres ; `round3/agent5.md` porte le verdict PARTIAL.

Reproduction hors ligne :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round3\build-judge.ps1'
```

Les huit journaux de production sont conservés. Multifibre compile01 est un succès avec des avertissements, compile02 échoue sur une normalisation numérique et une réécriture logarithmique déjà simplifiée, compile03/04 réussissent. QuotientGauss compile01/02 échouent sur des instances, des noms de lemmes et des réécritures/coercitions ; compile03/04 réussissent. Les preuves incomplètes imprimées dans les journaux échoués ne sont jamais acceptées. Ces trois échecs de compilation sont techniques ; la compensation locale favorable est, elle, réfutée mathématiquement.

Une source primaire récente a été contrôlée pour une autre route : [Banks–Shparlinski, Multiple sums with the Möbius function](https://arxiv.org/html/2506.08787v1), théorème 2.1 et §7.6. Le théorème concerne trois variables dans une somme additive séparée. Notre tentative d'identification échoue : le produit s*t reste un terme mixte, et le facteur lisse z n'a pas leur poids mu(z). Le résultat n'est donc pas utilisé comme borne du HH original. Les bornes de [Blomer–Pascadi](https://arxiv.org/html/2607.24311v1) et les [moyennes de Cantarini](https://arxiv.org/abs/2607.09110) ont été confrontées aux contrats antérieurs ; leurs coûts extérieurs ou leur moyenne sur N ne procurent pas le contrôle ponctuel requis ici.

## Boucle 4 certifiée : obstruction affine et complétion composite

Le Juge a recompilé séparément `round4/lean/AffineHHObstruction.lean` (9 théorèmes) et `round4/lean/CompositeCompletion.lean` (12 théorèmes). Les deux sources importent uniquement mathlib ; aucun ancien olean de recherche n'est chargé. Les 21 nouvelles conclusions ont les seuls axiomes propext, Classical.choice et Quot.sound. Les codes de sortie sont zéro, sans diagnostic, et les anciens builders et reçus restent inchangés. Le total distinct des quatre boucles est 90, attesté par leurs reçus séparés.

Le certificat affine suppose une identité A(X,Y)R(X,Y)+B(X,Y)S(X,Y)=N pour **tous** les paramètres du corps, avec N non nul et R,S partout définies. Il prouve le déterminant croisé nul des deux formes de branches opposées. Il ne formalise ni une extension depuis une boîte finie ni le lemme complet de rang total un. La différence mixte 1040 d'un tuple positif à N=10^8 est conservée. Le filtre rationnel passe 12 400 intersections ; le chart de rang un est testé en 303 points, avec seulement 101 valeurs distinctes du paramètre effectif X, et 25 faces carrées-libres/unitaires distinctes. Ce transfert affine précis ne fournit pas les gradients indépendants cherchés.

La complétion composite est prouvée pour tout q non nul, avec le caractère réel dans ZMod q et les vrais poids F,G. Elle conserve le défaut défini par la somme des fréquences nonunitaires :

    tau*H = q*F_moment - E_nonunit,
    (tau²/q²)*H_F*H_G = (F_moment-E_F/q)*(G_moment-E_G/q).

La reconstruction complète est déduite du DFT de mathlib. Aucune primitivité ni division par tau n'est ajoutée. Si tau=0, le corollaire conserve E=q*F_moment : le défaut peut porter toute la masse. La fréquence zéro appartient au défaut pour q>1. Un poids dépendant de C=s*t conserve cette dépendance.

Le filtre cyclotomique exact passe les modules 11, 15 et 100. Sur delta_1, la projection double limitée aux unités vaut respectivement 1, 1/25 et 0, tandis que la masse physique vaut 1. À N=10^8, une partition structurelle en orbites de cinq unités certifie la somme de Gauss nulle du caractère induit modulo cinq, sans prétendre énumérer les quarante millions d'unités. Figer la fenêtre C=33 à C=21 donne une masse 2 contre 1. Ces benchmarks sont des falsifications finies des simplifications proposées, pas une estimation asymptotique du support HH.

Le Juge a reproduit les deux JSON numériques à l'identique dans un dossier isolé, SHA256 compris. Les trois essais de compilation échoués sont archivés : inférence de paramètres implicites dans le module affine, fonction de reindexation et représentation du caractère inverse, puis commutativité résiduelle dans le module composite. Ces erreurs techniques ont été corrigées ; elles ne sont pas assimilées à une obstruction de parité. Les rapports `round4/agent3_formal_audit.md`, `round4/agent4_composite_completion.md`, `round4/agent6.md` et `round4/agent5.md` fixent les portées exactes.

Reproduction hors ligne :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round4\build-judge.ps1'
```

Les entrées de [uniformité supérieure de Möbius, I](https://arxiv.org/html/2204.03754v4) et [II](https://arxiv.org/html/2411.05770v2) ne sont pas transférées au niveau HH nonlinéaire fixé. La première requiert notamment des formes et longueurs admissibles ; la seconde donne des assertions pour presque tous les intervalles. Le rapport d'idéation distingue explicitement ces conditions du contrat ponctuel. Les estimations inverses de [Korolev–Shparlinski](https://arxiv.org/html/1804.01337v1) et de [Korolev](https://arxiv.org/html/1610.09171v1) ne sont pas appliquées aux poids HH : leurs hypothèses de longueur ou de multiplicativité ne sont pas vérifiées. Aucun résultat externe manquant n'est introduit comme axiome Lean.

## Boucle 5 certifiée : coordonnées de déterminant et défaut sur support unités

Le Juge a recompilé les fichiers `round5/lean/DeterminantCoordinates.lean` et `round5/lean/UnitSupportedCompletion.lean` : 15 et 11 théorèmes, codes de sortie zéro, aucun diagnostic ni preuve incomplète et uniquement les axiomes standards. La dépendance `CompositeCompletion` (12 conclusions) a été reconstruite depuis une copie exacte de la source finale de la boucle 4, sans réutiliser son ancien olean. Cette boucle audite ainsi 38 déclarations, dont 26 nouvelles distinctes ; avec les 90 précédentes, le total certifié séparément est 116. Le reçu `round5/judge_receipt.json` fixe les sources, hashes, sorties et filtres.

Le rapport sémantique final `round5/agent5.md` porte le verdict PARTIAL. Son builder vérifie les 120 fichiers figés avant et après compilation. Ce checkpoint conserve l'objectif de recherche actif ; il ne marque ni victoire ni clôture de la cible.

Le premier conserve le niveau u*B+s*D=N, B=b*v*x, D=k*t*z, et la matrice M=[[u,s],[-D,B]]. Les quotients A=(u+lambda*D)/N et C=(s-lambda*B)/N reconstruisent exactement M=H_lambda*G et det G=1 sous les divisibilités affichées. Le sens inverse et les quotients v,t sont prouvés. L'existence canonique 0≤lambda<N est dérivée de gcd(N,B)=1 par Bézout, et non postulée. Cela ne constitue pas une formalisation supplémentaire de toutes les fenêtres HH ni de leur somme finie pondérée.

À N=10^8, les deux bases du même H_lambda, lambda=73626461, sont vérifiées. Le changement de base de paramètre -78 conserve les masques de base, mais remplace v=7 par 75469=163*463 et s=7951 par 7717. Le produit des quatre vraies valeurs de Möbius du tuple développé passe de +1 à -1. Le coefficient agrégé H2(a)*H2(r) passe de 4 à 0 dans le filtre Python ; ce dernier calcul n'est pas annoncé comme un théorème du nouveau fichier Lean. Les logarithmes et ar changent aussi. Ce diagnostic réfute la constance automatique sur classe, sans réfuter une future annulation pondérée. La représentation brute centrale conserve un coût N^(5/4) avant logarithmes, sans nouveau gain.

Le second suppose F(z)=0 sur les nonunités du véritable ZMod q. Avec M=F_moment et les définitions de la boucle 4, il prouve :

    H = chi^(-1)(-1) * tau(chi) * M,
    kappa = chi^(-1)(-1) * tau(chi^(-1)) * tau(chi) = normSq(tau(chi)),
    E_nonunit = (q-kappa)*M.

Les deux sommes de Gauss demeurent distinctes. La conjugaison et le support sont prouvés, sans primitivité, borne de conducteur ni division par tau. La normalisation double conserve (kappa/q)^2*M_F*M_G. Kappa est réel non négatif ; le moment M reste complexe et signé, sans contrôle de taille. La théorie générale de l'induction par conducteurs C1–C6 du rapport d'idéation n'est pas attribuée à ce module.

Les deux filtres exacts sont PASS avant compilation. `round5/hecke_checks.py` parcourt les 204 shears positifs déclarés ; 43 respectent les masques de base, avec 24 signes positifs et 19 négatifs. `round5/frequency_checks.py` teste 89 988 égalités rationnelles sur 7 499 fréquences échantillonnées et les 81 strates q divisant N=10^8. La cardinalité totale N de la partition est structurelle, pas une énumération des cent millions de fréquences. Pour le caractère induit modulo cinq, l'argument d'orbites ne laisse que huit fréquences actives : q=5 et q=10 portent chacun 50 millions fois le moment physique. Le défaut conserve ainsi toute la masse lorsque tau_N=0.

Le Juge a rejoué les deux bancs dans un dossier isolé ; leurs JSON ont les mêmes champs et SHA256 que les originaux. Les 120 anciens artifacts suivis demeurent inchangés. La première compilation de coordonnées échoue sur 0-D non simplifié ; les suivantes réussissent, puis ajoutent le certificat concret des deux bases. Les trois échecs de complétion sur support unités concernent l'ordre des facteurs après conjugaison et une réécriture négative récursive ; la quatrième compilation et le rejeu frais réussissent. Ce sont quatre erreurs techniques archivées, distinctes des falsifications arithmétiques. Les rapports de production détaillent aussi les limites non formalisées.

Reproduction hors ligne :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round5\build-judge.ps1'
```

Les caractères d'ordre quatre modulo 5 et 10 distinguent réellement tau(chi) de tau(chi^(-1)), et valident le facteur kappa par phases cyclotomiques modulo 20. Supprimer le support unités est falsifié par delta_2 modulo 10. Pour N=70630 et h=2, le conducteur 5 conserve un module additif q=35315 avec contribution non nulle. Les petits modules 15,100,385 sont des benchmarks distincts et complets. Le contrôle de conservation retrouve les SHA256 des 120 anciens fichiers suivis, en excluant explicitement le rapport vivant, l'état du contrôleur et les caches.

Le [chapitre original de Montgomery–Vaughan, théorèmes 9.10 et 9.12](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf) justifie les formules de Gauss induits utilisées dans l'idéation. Les strates actives d'un profil physique d'unités portent le même moment avec des coefficients positifs dont la somme est N. Cette descente ne crée donc aucune annulation entre strates ; une borne du moment physique demeure nécessaire. Les acquis de petits conducteurs et de masque croissant sont conservés avec leur onset, sans être importés dans les grands conducteurs.

## Travail encore nécessaire après la boucle 5

L'observation suivante doit évaluer des autocorrélations de dilatations premières du vrai profil arithmétique, avec sa normalisation, plutôt qu'une hypothèse favorable de signe local. Le [critère fini de Bourgain–Sarnak–Ziegler, théorème 2](https://arxiv.org/pdf/1110.0992), demande des corrélations contrôlées et un seuil dépendant de la précision. Son application aux horocycles ne donne pas de taux utilisable ici. Faire dépendre la précision de log N exige de vérifier les longueurs de sa décomposition, les diagonales et le support restant ; les grands nombres premiers ne peuvent être omis du profil. Une conclusion qualitative ou un lemme conditionné directement à l'estimation souhaitée ne constituerait pas la victoire.

Un autre secteur testable est le préfixe carré-libre tordu par un caractère nonprincipal avec masque multiplicatif fixe. Sa borne périodique élémentaire ne s'étend pas automatiquement aux masques additifs et aux poids HH couplés. Ce secteur doit être distingué du cumul original complet. Les sélecteurs, non-unités, diagonales et coûts extérieurs restent dans le contrat.

Le détecteur local et l'inversion quartique sont vérifiés. Ils ne prouvent ni un gain sur le moment additif aux grands modules, ni la compensation des commutateurs et des défauts de frontière. Le pont couvert et le paiement de 2 max(e,0) doivent rester ceux du même contrat. La cible D_N≤N/(256 log N log log N) demeure non démontrée.

La prochaine observation doit porter sur la combinaison signée complète et sur la projection de son véritable coefficient arithmétique, après les soustractions de diagonales exigées. Il faut un lemme arithmétique indépendant : une hypothèse qui reformule exactement la cible ne suffit pas. Les arbres, rapports des six rôles, scripts, logs et reçus préservent ce point de reprise dans `.arbor/sessions/parity`.

## Boucle 6 : contrats falsifiés avant compilation

Cette boucle conserve l'objectif original et n'ajoute aucun théorème auxiliaire pour lui substituer une réussite de compilation. Les deux formalistes ont audité les énoncés proposés avant le compilateur ; les versions fausses ont été éliminées par le filtre arithmétique exact. Le compteur reste neuf modules Lean et 116 conclusions auxiliaires des cinq premières boucles. Aucune nouvelle certification Lean ni erreur de compilateur n'est alléguée.

Le profil raw est celui du pont complet, sans masque mu(n)^2 ajouté. L'Agent 1 a conservé la couverture exacte de l'amplificateur fini : a_X*S_X=-T_X+R_X. À N=100000000, X=303 et P={2,5}, le vrai profil donne

    S_303 = -(1/2) log(99999697) log101 < 0,
    a_303 = 211/303, T_303 = G_sf = 0,
    R_303 = (211/303)*S_303 != 0.

Les dilatations nulles par les premiers divisant N ne couvrent aucune contribution du profil unitaire. Le raccourci supprimant R est donc faux ; l'identité d'amplification reste correcte. La queue de 99 999 696 arguments n'est pas calculée. Le raccord requis demeure D_N=(T_X-R_X)/a_X-S_tail+2 max(e,0), avec des estimations indépendantes de ces charges. Les normes, diagonales et puissances premières ne sont pas supprimées.

Le contrôle retient notamment n=9967²=99341089, m=658911=3*11*41*487 : mu(n)^2=0 mais F_N(m)>0, certifié par des intervalles rationnels. Le point m=311 du profil raw et le tuple HH positif non couvert restent distincts. Le [critère BSZ, théorème 2 et sa preuve](https://arxiv.org/pdf/1110.0992) ne fournit pas la calibration variable tentée : au budget considéré, son premier intervalle commence au-delà de N. Ce diagnostic n'exclut pas une autre partition finie, ni toutes les méthodes de dilatations.

Pour la seconde piste, les quatre signes sont conservés dans A=buv, C=kst, A*x+C*zeta=N. Le contrat CRT proposé omettait gcd(d,ell)=1. Le témoin A=273, C=10403, d=ell=11, e=f=1 respecte les conditions écrites mais donne M=3003 et gcd(C*f*d²,M)=11, qui ne divise pas N. La cellule est vide, et son inverse n'existe pas. Le corrigendum de l'Agent 4 ajoute la compatibilité avant inversion ; la version générale utilise L=lcm(d²,f), M=lcm(A,e²,ell), g=gcd(C*L,M), puis réduit modulo M/g seulement si g divise N. L'hypothèse gcd(C,N)=1 héritée des unités est écrite explicitement.

Le cas e=3 partageant A=273 donne M=819 et 12 points dans 1<=zeta<=9612 ; le module produit erroné n'en conserve que quatre. Ce sont des cellules signées de l'expansion, pas des points HH carrés-libres. Le twist isolé varie sur les points admissibles de la fenêtre testée ; le produit complet chi(A)chi(x)conj(chi(C))conj(chi(zeta)) vaut pourtant chi(-1), soit +1 pour le caractère quadratique et -1 pour l'ordre quatre modulo cinq. Une oscillation du seul facteur zeta ne peut être créditée à ce secteur compensateur.

La longueur pertinente est le nombre de points de la progression de pas A, avec son +1. Dans la fibre admissible A=1113121, C=213, le domaine brut 1..464257 contient exactement zeta=244769, x=43, bien que N/(AC)=100000000/237094773<1. La borne de caractères envisagée ne fournit pas de gain uniforme après conservation de cette longueur et des coûts extérieurs dans la boîte revue. Les queues carrées, la variation, la rugosité, zeta=1 et les secteurs de grands conducteurs restent à payer ; aucune impossibilité globale n'est conclue.

Les scripts finaux sont `round6/katai_checks.py` et `round6/squarefree_checks.py`. Le premier vérifie les identités de couverture et de Gram aux préfixes 303,512,1024 déclarés. Le second vérifie 1066 cas finis, 23544 cellules signées brutes et 558 cellules CRT compatibles. Les calculs utilisent des entiers, rationnels, coefficients de logarithmes symboliques et entiers de Gauss ; les signes logarithmiques ont des intervalles rationnels. Les domaines et limites sont dans `round6/agent6.md`. Ces PASS portent sur les identités corrigées et les falsificateurs ; ils ne valident aucun gain analytique.

Le Juge indépendant a rejoué les deux JSON intégralement et reproduit leurs SHA-256, avec code de sortie zéro. Les 160 fichiers antérieurs ainsi que les sources et reçus de cette boucle sont inchangés avant/après. `round6/agent5.md` et `round6/judge_receipt.json` portent REJECTED_BEFORE_COMPILATION pour les raccourcis faux, victory=false, score=0, lean_invoked=false. Ce score mesure l’absence du mécanisme demandé, pas le succès du gate exact.

Reproduction du gate préalable, sans invocation Lean nouvelle :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round6\audit-judge.ps1'
```

Les 160 artefacts antérieurs inventoriés sont inchangés. Les corrections concernent les candidats de cette boucle, pas les acquis fournis. Le bloc de questions est sauvegardé séparément dans `round6/PROBE_BLOCK.md`, afin de conserver l'ancien CONTRACT.md figé.

## Point de reprise après la boucle 6

L'objectif reste actif. Les erreurs de couverture, d'inversion et de caractère sont maintenant explicites ; elles ne remplacent pas le problème arithmétique. La prochaine piste doit établir une estimation indépendante des corrélations utiles ou d'un regroupement signé de plusieurs fibres avant la prise des valeurs absolues, avec les quatre coefficients de Möbius et tous les sélecteurs. Le pont couvert, la queue, les secteurs principaux et 2 max(e,0) restent intégralement dans l'obligation. Aucune borne nouvelle sur D_N ni victoire n'est établie.

## Boucle 7 : couverture complète et raccord natif

Cette boucle apporte un paiement analytique partiel écrit et un falsificateur supplémentaire, sans nouvelle certification Lean. Les deux formalistes ont audité les contrats exacts. Le Juge a rejoué les trois bancs finis indépendamment, avec sorties isolées et empreintes identiques. Le compteur demeure neuf modules Lean et 116 conclusions auxiliaires ; la cible sur D_N reste ouverte. Les raccourcis précis rejetés ne sont pas assimilés à des erreurs renvoyées par Lean : aucun candidat admissible n'a été soumis au compilateur dans cette boucle.

La couverture complète répare le défaut d'incidence de la boucle 6. Pour le même profil raw F_N, sans nouveau filtre mu(N-m)^2 et avec F_N(1)=0, les identités exactes sont

    mu(m) log m = -sum_(d|m) mu(m/d) Lambda(d),
    S_full = -sum_(p^j*l<N) mu(l) log p/log(p^j*l) F_N(p^j*l).

Après cancellation prouvée des puissances, on peut écrire

    S_full = -sum_(p*l<N, p prime, p ne divise pas l)
                  mu(l) log p/log(p*l) F_N(p*l).

La condition p ne divisant pas l est essentielle. Les témoins actifs m=841=29² et m=10201=101² ont mu(m)=0 mais F_N(m) non nul ; les deux coefficients -1/2,+1/2 de la couverture complète s'annulent. Remplacer Lambda par les seuls premiers sans cette condition créerait un terme fictif. Les puissances propres du premier axe demeurent dans F_N, dont les masques et fronts sont évalués à l'argument entier p^j*l ou p*l.

La représentation de Mellin donne S_full=-integral_0^infinity A(t)dt, avec

    A(t)=sum_(p^j*l<N) mu(l) log p F_N(p^j*l)(p^j*l)^(-t).

Elle est exactement A(t)=S'(t), pour S(t)=sum_m mu(m)F_N(m)m^(-t), donc cette représentation standard ne fournit pas à elle seule une oscillation nouvelle. Une queue peut toutefois être payée indépendamment. La face stricte impose F_N(m)=0 pour m<=alpha. La norme réelle de la boucle 6 et Cauchy donnent sum|F_N|<=sqrt(20)u²(N-1)(1+u)^(3/2). Avec

    B=1024 sqrt(20)u³(1+u)^(3/2)ell, T=(4/u)log B,

sous u>1 et B>1, alpha>=exp(u/4) donne

    |integral_T^infinity A(t)dt| <= N/(1024u ell).

Cette dérivation a été auditée par l'Agent 3 ; elle n'est pas un théorème Lean ni un résultat numérique asymptotique. L'intégrale de 0 à T reste à contrôler avec son signe. Pour p de taille comparable à N, son secteur l=1 garde le poids 1-p^(-T), proche de 1 ; la queue payable ne le supprime pas.

Définir C1=sum_(p<N,p premier)F_N(p) conduit au raccord exact

    S_full=-C1+S_rest,
    D_N=C1-S_rest+2max(e,0).

L'audit mathématique établit un minorant qualitatif C1>=N log N/384 **éventuellement, pour N pair et 3 ne divisant pas N**. La dérivation conserve le préfixe quartique réel R>=N^(1/12)/4, puis log R>=u/13 et le masque K=(N-p)N<=R^26. Elle utilise la Lemma 10.1 acquise avec l'endpoint log(R/p)A_K(R), le produit singulier S(K)=O(log log N), puis le PNT aux classes fixes modulo 3 sur p dans [N/3,N/2], p congru à N modulo 3. Les unités et les petits premiers sont payés avec les marges détaillées dans `round7/agent3_contract_audit.md`. Le [théorème de PNT en progressions de Kedlaya, 4.12](https://kskedlaya.org/ant/chap-primes-in-ap.html), est le comptage fixe utilisé ; aucune hauteur eighth de Theorem 10.2 n'est transférée au profil quartique.

Le seuil global de ce minorant n'est pas évalué : il ne donne aucune validité dès u=1024 ou au point N=10^8 et n'est pas certifié par Lean. Il écarte seulement un paiement absolu séparé de C1 dans le budget cible sur cette sous-famille. Il laisse ouverte une compensation signée par S_rest. La couverture complète elle-même n'est pas rejetée.

La seconde piste introduit des caractères pour un premier p ne divisant pas N. Sur les seuls tuples physiques avec p ne divisant pas n*m, l'orthogonalité reconstruit exactement leur masse principale T0 par la somme des p-2 modes nonprincipaux. Avec les exceptions R_p, elle donne C_HH=R_p+T0 ; le résidu centré conserve encore **-M_HH**. Une somme de Jacobi complète vaut -chi(-1), mais la reconstruction de tous les modes vaut p-2, la masse principale exacte. La centration jointe possède une discrepancy de préfixe <=2 pour une pente unitaire ; ce coût reste par cellule, avec tous les coûts extérieurs, la variation et chaque +1. Les pentes nonunitaires sont conservées comme exceptions. Aucun petit cumul signé HH n'en découle.

Le raccord à la vraie ligne du crible est différent. Sur les unités n,N modulo k, cette ligne contient

    chi(n) conjugate(chi(N)),

alors que le twist tenté contient chi(n) conjugate(chi(m)). Le tuple réel

    b=101, u=103, v=107, x=43, k=7, s=3, t=71, zeta=34967,
    n=47864203, m=52135797, r=7447971

conserve les masques prescrits et les quatre signes, dont le produit vaut +1. Tous les nouveaux twists modulo 7 sont nuls puisque 7 divise m ; la ligne native vaut pourtant 5/6. La substitution est donc fausse. Les exceptions R_7 portent toute cette fibre, elles ne sont pas supprimées. La trace P_q antérieure reste un acquis, sans oscillation nouvelle revendiquée.

Les diagnostics Jacobi complets pour p=3,7,13 et C=10403 sont des contrôles de normalisation sans le masque A=273 : p divise A, donc ils ne sont pas des cycles admissibles de cette fibre p-unitaire. Le banc CRT p=11, M=819 conserve ses douze cellules signées ; ce ne sont pas douze tuples HH carrés-libres. Les lcm, la compatibilité g|N avant inversion, les masques exacts, zeta=1 et les comptages +1 sont conservés.

Le Juge reproduit intégralement `round7/logarithmic.json` (PASS_IDENTITY_ONLY), `round7/jacobi.json` (PASS_IDENTITIES_ONLY) et `round7/trace.json` (PASS_EXACT_CONNECTION_ONLY), chacun avec son SHA-256. Les domaines comprennent 19999 arguments de convolution, 65533 termes de puissances premières, 44944 préfixes cyclotomiques rationnels, cinq tuples HH pondérés, 64 lignes natives et 7394 cas de la trace acquise. N=100000000 est fixé dans les bancs ; ils ne calculent pas tout S_full ou D_N. Les 190 artefacts antérieurs suivis restent inchangés avant et après.

`round7/judge_receipt.json` consigne REJECTED_BEFORE_COMPILATION pour les transferts non justifiés, lean_invoked=false, compiler_exit_code=null, victory=false et score=0. Le paiement de queue analytique et le minorant qualitatif sont distingués explicitement de la certification Lean. Le score zéro mesure l'absence de victoire, pas un échec des identités corrigées.

Reproduction hors ligne du gate exact, sans nouvelle compilation Lean :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round7\audit-judge.ps1'
```

## Point de reprise après la boucle 7

L'objectif demeure actif. Le morceau signé de Mellin proche de zéro et la compensation C1-S_rest restent à démontrer par une information arithmétique indépendante. Le prochain mécanisme doit traiter simultanément la contribution physique et son modèle harmonique avec les facteurs natifs, les secteurs principaux et nonunitaires, les masques et 2max(e,0). Les identités standard acceptées et les falsificateurs précis sont conservés ; aucune impossibilité générale ni victoire n'est déduite. L'idéation suivante est lancée sur cette compensation signée.

## Boucle 8 : tête physique payée, reste signé conservé

La huitième boucle établit une borne analytique partielle écrite pour la tête physique, après réemploi exact du paiement acquis de I. Les deux audits conservent tous les frais et un seuil supplémentaire de Bombieri–Vinogradov non évalué. Aucune nouvelle preuve Lean n'est soumise : neuf modules et 116 conclusions auxiliaires restent certifiés des boucles précédentes. Le verdict sémantique est PARTIAL_HEAD_GAIN_WITH_OPEN_SIGNED_REMAINDER, victory=false et score=0.

Pour le même profil quartique complet, les identités R1–R3 de `round8/agent1_signed_compensation.md` donnent

    S_full = S_Lambda - I,
    D_N = -S_Lambda + I + 2 max(e,0),
    S_Lambda = -sum_k mu(k)^2 P_k + sum_k mu(k)/phi(k) M_k.

Les deux lignes physiques P_1 et harmoniques M_1 sont identiques. Leur cancellation conjointe laisse exactement

    D_N = P^{>=2} - M^{>=2} + I + 2 max(e,0).

Le paiement global de I concerne la même somme complète. Le réutiliser ne permet pas de redistribuer gratuitement un ancien paiement du modèle à sa version amputée de k=1. Les puissances propres du premier axe restent dans Lambda_N ; aucun masque mu(n)^2 n'est ajouté.

La coupe auxiliaire est H=floor(N^(3/8)), B_cut=floor(N^(1/32)), avec B_cut distinct du B de la monographie. L'expansion de mu(k)^2 garde gcd(d,rN)=1 avant de former les modules q=r*d^2*t. Sur le support carré-libre, le regroupement b=d*t, c=r/t, g=t donne q=b^2*c et le poids

    w_(alpha,H)(b^2*c)
      = mu(b) mu(c) sum_(g|b, alpha<c*g<=H) mu(g) log(c*g).

Les fibres coupées restent littérales. La formule de fibre complète, log(c) pour b=1 et -Lambda(b) pour b>1, n'est appliquée que lorsque toutes les faces requises sont satisfaites. La partie b<=B_cut a q<=N^(7/16), dans la portée qualitative de BV. Le préfixe positif particulier contient floor((N-2)/q) points, donc <=N/q ; les autres comptages de progressions gardent leur +1.

Deux queues indépendantes sont payées avant toute compensation :

    E_phys <= 2 N u^2 (1+u)(2+u)/B_cut,
    E_main <= 9 N u (1+u)(2u^2+7u+8)/B_cut.

Le principal eulérien est traité par le Mertens masqué acquis. Sa convolution possède les moments sum|h(d)|/d<2 et sum|h(d)|/sqrt(d)<4, audités avec l'indice p-1 dans les comparaisons locales. La sommation d'Abel garde les endpoints. Le reste de progressions est traité par BV all-prefix pondéré : tau(q)^2<=d_4(q), séparation selon tau(q), et retrait explicite des bases p divisant N. Aucun caractère exceptionnel n'est supprimé. Le coût élémentaire de ce retrait est au plus (u^3/log 2) Q0(1+u), Q0=B_cut^2 H.

L'audit `round8/agent3_contract_audit.md` valide ainsi une borne qualitative indépendante P_head_all=O_A(N/u^A), et la même conclusion pour k>=2 après paiement de H*u^2. Cette application de BV et Mertens est un progrès local dans l'architecture ; elle n'est pas présentée comme une identité nouvelle contournant la parité. Son seuil BV et ses constantes ne sont pas chiffrés. Elle ne donne donc pas un paiement calibré dès l'onset acquis u>=10^24, ni à N=10^8, et n'est pas certifiée en Lean.

Le raccord restant est exactement R16 :

    D_N = P_head^{>=2}
          + [P_tail^{>=2} - M^{>=2}]
          + I + 2 max(e,0).

La différence entre crochets demeure non estimée. Pour k=3, elle contient notamment mu(r)*Lambda(N-3r)*log r sur r>H, avec les faces et unités originales. BV appliqué aux progressions sans ce coefficient ne contrôle pas cette corrélation. La prochaine preuve doit apporter une information arithmétique indépendante sur cette différence, payer 2 max(e,0), puis calibrer les frais au domaine revendiqué.

La seconde piste étudie le facteur natif G_chi(a,b)=chi(N-a*b)*conjugate(chi(N)) sur tous les résidus modulo un premier q ne divisant pas N. Pour chi nonprincipal, son Gram exact est q I-w w*, w_a=chi(a), y compris les axes nuls. Sa norme vaut sqrt(q). Les facteurs locaux principaux d'un caractère induit sont conservés : leur norme rho_p est strictement entre p-1 et p, et ne reçoit pas fictivement un facteur sqrt(p). Le Gram exact ne suffit pas pour le coefficient couplé F_N(h*l), et encore moins pour le cumul HH pondéré.

L'audit `round8/agent4_contract_audit.md` retient deux falsificateurs précis. Une matrice couplée bornée W=G produit q^2-q+1>q*sqrt(q), réfutant le transfert d'une borne séparable à tout coefficient borné. Le vrai mineur L2 utilise les premiers h=3,13 et l=101,311 ; les arguments m=303,933,1313,4043 donnent un déterminant non nul. Le premier axe n=N-1313 est non carré-libre et reste dans le profil raw. Ces témoins excluent les raccourcis proposés, sans exclure une autre décomposition riche et cohérente. Sur toute fibre physique avec q divisant k, n=N-r*k est congru à N modulo k, donc le facteur natif vaut exactement 1. Sa norme de Gram n'y crée aucune oscillation.

Les bancs finis à N=100000000 retiennent trois erreurs concrètes de coupe :

- r=303, k=63 : omettre gcd(d,r)=1 avant le produit d^2*t donne le coefficient -1 au lieu de 0.
- m=112211=11*101^2 : à B_cut=1, tête -log101 et queue +log101 sont non nulles et se compensent ; mu(m)^2 ne peut pas être ajouté à cette tête coupée.
- m=173 : la ligne k=1 est non nulle et doit être retirée ou annulée conjointement avec son modèle.

Le Juge indépendant a reproduit tous les champs et octets des trois JSON : `compensation.json` (PASS_EXACT_IDENTITIES_ONLY), `head_regrouping.json` (PASS_HEAD_IDENTITY_ONLY) et `native_gram.json` (PASS_ALGEBRA_ONLY), code de sortie zéro. Les domaines comprennent 65536 couples de bascule, douze arguments sélectionnés pour les fibres de tête, 9339 entrées de Gram premier et 6120 entrées CRT. Ils ne calculent ni tout D_N ni toute la tête, et ne valident aucun budget asymptotique. Les 227 artefacts antérieurs sont inchangés avant et après le rejeu.

Les pages physiques 32,33,36 du PDF original ont également été reproduites indépendamment, avec les mêmes empreintes des PNG, textes et reçu. Elles confirment u>=10^24 ; l'ancienne lecture u>=1024 provenait d'un exposant aplati par l'extraction. Les sources et anciens reçus restent inchangés, et l'annotation au début de ce rapport corrige uniquement cette lecture. Les constantes de budget 1024 restent distinctes.

`round8/judge_receipt.json` distingue la tête analytique partielle, la borne arithmétique pondérée manquante pour le Gram, et l'absence de certification nouvelle. lean_invoked=false et compiler_exit_code=null : aucune erreur de compilateur n'est inventée. Le gate exact peut être reproduit hors ligne par :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round8\audit-judge.ps1'
```

## Point de reprise après la boucle 8

L'objectif demeure actif. Le prochain mécanisme doit contrôler la différence signée de R16 avec le modèle complet correspondant, les quatre signes de Möbius lorsqu'il passe par HH, les secteurs principaux et nonunitaires, les fronts et 2 max(e,0). Le paiement local de tête et les falsificateurs sont conservés. Aucune cible globale, impossibilité générale ou victoire Lean n'est déduite.

La neuvième idéation est lancée par les deux rôles dédiés : regroupement conjoint du long physique et de son modèle, et estimation d'un opérateur réellement pondéré. `round9/PROBE_BLOCK.md` fixe les questions et le périmètre. Le rôle numérique et les formalistes prendront la suite par vagues, selon les contrats proposés. Le checkpoint actif indique les rôles effectivement en cours ; aucune neuvième boucle terminée ou candidature Lean n'est encore annoncée.

## Boucle 9 : transport conjoint et paiement du premier axe properpower

La neuvième boucle conserve le cadre source et rapproche le reste d'un moment sur le premier axe premier. Les deux formalistes ont audité deux paiements indépendants écrits : le défaut harmonique d'un déplacement conjoint de face, et les puissances premières propres du premier axe. Aucun nouveau certificat Lean n'est produit et aucune victoire n'est établie. Neuf modules et 116 conclusions auxiliaires historiques demeurent inchangés.

L'auxiliaire a9=ceil(N^(7/16)) modifie simultanément les deux faces a*k<m des noyaux D_a et W_a. Alpha, Q, I_alpha et e originaux restent intacts ; Q ne devient pas floor((N-1)/a9). Pour les mêmes points, masques et caps, le transport corrigé est

    S_Lambda^alpha-S_Lambda^a9 = -P_bande^all-Z_face^all,
    Z_face^all = sum_m mu(m)Lambda_N(N-m)(W_alpha-W_a9).

Les lignes k=1 des deux bandes s'annulent conjointement. Le raccord avec le déficit initial devient donc

    D_N = B_a9 + P_bande^{>=2} + Z_face^{>=2}
          + I_alpha + 2max(e,0),
    B_a9 = P^{a9,>=2}-M^{a9,>=2}.

L'appairage signifie la même face a9*k<m ; il ne crée pas une bijection entre le modèle libre et les multiples kr physiques. La première formule de bande V1 avait oublié l'unité de k en utilisant Lambda ordinaire. À N=100000000, n=2,r=161,k=621118, elle ajoutait log2*log161 alors que Lambda_N(2)=0. V1 reste documentée comme ERROR_FALSIFIER. V2 garde Lambda_N ou les deux unités explicites et passe les identités finies corrigées. Il s'agit d'une faute de support, sans prétendue erreur Lean ni remise en cause d'un acquis.

Le progrès indépendant du transport est le paiement de Z_face. Sur m>=ceil(N^(3/4)), les deux préfixes exacts R_a=min(Q,floor((m-1)/a)) sont au moins N^(1/5). Le même K=(N-m)N est positif pair et <=N^3. La phase source W_K(R)+log(R/m)A_K(R) conserve son endpoint, et ses deux principaux S(K) s'annulent. La petite face utilise directement sum1/phi(k)<=3(1+u). Les deux régions donnent

    |Z_face^{>=2}| <= E_Z9,
    E_Z9/N = 8*10^8*u^5*exp(-sqrt(u)/60)
              +320*u^2*exp(-u/40)
              +12*u^2*(1+u)*exp(-u/4).

L'audit3 vérifie les préfixes entiers, chaque constante, les endpoints et la décroissance. Sous les inputs acquis et u>=10^24, E_Z9<10^(-12)N/(u ell). La page 27 originale confirme que (54) contient exp(-sqrt(u/60)) : le majorant ci-dessus emploie un affaiblissement valide, explicitement distingué de la formule source. `round9/SOURCE54_CLARIFICATION.md` conserve cette lecture avec les pixels et leurs empreintes.

La bande physique est payée qualitativement par le mécanisme de tête, avec ses vraies fibres coupées q=b^2*c et une coupe auxiliaire B9_aux=floor(N^(1/64)). Les modules satisfont q<=2N^(15/32). Les deux queues restent distinctes, ainsi que le principal eulérien, les endpoints Mertens, le BV all-prefix pondéré et le coût a9*u^2 de retrait du k=1 physique. Pour chaque A fixé, le gain écrit est O_A(N/u^A), mais son nouveau seuil BV et ses constantes ne sont pas évalués. Cette borne ne reçoit pas gratuitement une validité effective dès l'onset de I.

L'autre piste garde le coefficient entier du reste initial R16, avec physique à r>H et modèle entier au front alpha. Après la réécriture avec mu(m), la mesure positive du Gram peut légitimement porter Lambda_N(N-m)*mu(m)^2. Elle ne porte aucun mu(n)^2 et ne s'applique pas à une tête coupée en b. Le Gram conserve DD-DM-MD+MM, ses deux fronts différents, les diagonales et les vraies valeurs mu(k). L'identité d'énergie est standard ; sa positivité ne fournit ni signe au premier moment ni petite énergie première.

Son paiement arithmétique indépendant concerne les propres puissances n=p^j,j>=2 du PREMIER axe. Les bornes entièrement explicites sont

    tau(z) <= 2^2040*z^(1/8), z>=1,
    sum_(k<=Q)1/phi(k) < 3(1+u),
    sum_(n<N,n properpower)Lambda(n) <= sqrt(N)*u^2/log2.

Pour chaque n admis, le physique est majoré par u*Lambda(n)*tau(m), le modèle par u*Lambda(n)*sum1/phi(k). Il en résulte

    |B_pp| <= sqrt(N)*u^3/log2
                 *[2^2040*N^(1/8)+3(1+u)]
            <= N/(1024u ell), dès u>=65536.

Les formalistes3/4 vérifient les constantes et les exposants. Aucune constante C_epsilon inconnue ni petite énergie supposée n'entre dans ce paiement. N=10^8 est sous ce seuil ; les tests finis ne le valident pas. Ce résultat écrit demeure sans certificat Lean.

Les deux pistes n'utilisent pas le même reste : B_H=P_tail^H-M_alpha diffère de B_a9=P^a9-M_a9. L'audit3 prouve directement que les mêmes deux majorants positifs s'appliquent aux propres puissances de B_a9, avec ses fronts et ses caps, sans comparer les deux sommes signées. La même allowance est ainsi utilisée UNE fois dans le ledger choisi. Le raccord consolidé exact est

    D_N = B_prime^{a9}+B_pp^{a9}
          +P_bande^{>=2}+Z_face^{>=2}
          +I_alpha+2max(e,0).

Le moment B_prime^{a9}, la calibration effective de la bande physique et le paiement du bridge restent ouverts. On ne déduit aucune cible globale de ces paiements partiels. Pour k=3 et 3 ne divisant pas N, une ligne du nouveau reste est exactement (B_{-N mod3}-B_0)/2, avec B_c conservant mu(m)Lambda_N(N-m)log(m/3) et m>3a9. À N=10^8, m=32421 donne un terme positif nuisible ; m=9507 un terme négatif favorable. Ces deux signes réfutent une faveur pointwise uniforme, sans exclure une compensation globale.

Le banc neuf conserve le transport sur m=1..1024 et douze points déclarés, et le Gram sur cinq m et J={3,7,11,13}. Le faux témoin premier m=311 est corrigé : N-m=113*199*4447, donc Lambda_N=0 malgré un raw actif. Le vrai modèle-seul m=323 a un premier axe premier et une diagonale positive. Les properpowers n=9967^2 et n=9949^2 restent présentes. Au point m=2121, les bandes ALL-k et k>=2 sont distinguées ; au point m=1017399, la bande physique est nulle mais le modèle varie réellement. Aucun domaine fini ne représente tout D_N.

Le Juge indépendant a rejoué `round9/new_contract_checks.py` avec des sorties isolées : code0, tous les champs et octets du JSON identiques. Il reproduit aussi les pixels, le texte et le reçu de la page27 depuis le PDF original. Les deux PASS_IDENTITY_ONLY corrigés et les deux ERROR_FALSIFIER initiaux sont conservés sans exclusion. La borne analytique properpower reste explicitement hors du test numérique. Les307 fichiers protégés, dont les54 fichiers8 et les PNG/.olean antérieurs, sont intacts avant/après ; aucun fichier antérieur ajouté n'est admis silencieusement.

Le verdict `round9/judge/judge_receipt.json` est PARTIAL_PAYMENTS_WITH_OPEN_PRIME_SIGNED_MOMENT, score0, victory=false, lean_invoked=false et compiler_exit_code=null. Les paiements écrits ont leurs domaines propres ; ni un test Python ni une compilation générique ne leur substituent la victoire. Reproduction hors ligne du seul banc neuf et de sa liaison à la source :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round9\judge\audit-judge.ps1'
```

## Point de reprise après les audits de boucle 9

L'objectif reste actif. La prochaine recherche doit viser le moment PREMIER signé du modèle réellement apparié, en gardant les secteurs principaux, nonunités, faces, quatre signes HH et coûts extérieurs. Les paiements de face et properpower sont conservés, avec leurs domaines précis. Les identités standard de Gram et de transport, les PASS finis et les bornes auxiliaires ne remplacent pas un mécanisme de parité certifié Lean.

## Boucle 10 — identités natives certifiées, compensation signée ouverte

**Verdict final du Juge : PARTIAL_NATIVE_COFACTOR_IDENTITIES_WITH_OPEN_SIGNED_COMPENSATION ; score 0, victoire fausse.** Les six rôles ont terminé. Le Juge a reconstruit les deux sources finales dans un dossier neuf, avec Lean 4.15.0 et le cache mathlib local, sans anciens oleans personnalisés. Il a imprimé les axiomes de chacune des 25 déclarations : seulement propext, Classical.choice et Quot.sound, ou un sous-ensemble. Le cumul indépendant est onze modules et 141 conclusions auxiliaires. Le manifeste contrôleur lie les sources, reçus, sorties et empreintes finales.

| Nouveau module | Conclusions | Résultat indépendant | Portée |
| --- | ---: | --- | --- |
| round10/lean/PrimeCofactorIdentity.lean | 8 | Exit 0, quatre avertissements de prémisses source redondantes | E3 sur le vrai Möbius, Mangoldt et modèle totient/unitaire, c=1 et c non carré-libre conservés |
| round10/lean/ShortDivisorComplement.lean | 17 | Exit 0, sans avertissement | U1, diviseurs complémentaires, cap original, front strict, zéro non carré-libre et raccord physique d'unités |

La première identité s'écrit, pour p premier et 1<=c<=a<p, c<=Q,

    P_a(p*c) = -mu(c)[Lambda(c)+1_(c=1)log p],
    b_a(n,p*c) = mu(c)log n
                 [W_positive(n,p*c)-Lambda(c)-1_(c=1)log p].

P_a est le physique mu(m) fois la somme sur les diviseurs capés au front strict, avec log(m/k). W_positive conserve les k libres, la totient, gcd(k,nN)=1 et le même front. Ce bracket entier est nul si c n'est pas carré-libre ; la somme brute n'est pas annulée par cette affirmation. Le terme c=1 garde -log p. La représentation c<=a<p est canonique. Le résultat local n'a pas besoin de la primalité de n ; cette condition reste requise pour les secteurs analytiques du premier axe.

U1, avec la convention source log(k/m), est

    -mu(m)D_a(m) = mu(m)^2[-Lambda(m)-U_a(m)],
    U_a(m) = sum_(r|m, r<=a) mu(r)log r.

La preuve garde les quotients entiers, m=1, le cap Q original et la frontière stricte. Le wrapper physique prouve que tout k|m est unitaire à nN lorsque m+n=N et gcd(n,N)=1. Ce retrait de masque sur les seuls diviseurs physiques ne retire aucun k libre du modèle.

**Portée du préfixe à conserver :** U_a contient aussi les r<=alpha. La bande alpha<r<=a déjà étudiée ne paie pas cette partie basse. Toute réduction ultérieure doit garder son principal de référence et son raccord au modèle ; l'identité U1 ne transforme pas le paiement de l'annulus en estimation de tout U_a.

### Réduction unilatérale et charges écrites

Avec a=ceil(N^(7/16)), a^3>N donne au plus deux facteurs premiers de m au-dessus de a. Sur J2, m=c*p*q, a<p<q et c<N^(1/8)<a, tous les diviseurs du cœur sont présents. Le coefficient entier devient C=Lambda(c)+mu(c)W_kernel. Cette complétude ne vaut pas sur toutes les fibres J1,c>a.

Sur le bulk m>=ceil(N^(3/4)), n=N-m>Q premier, le masque harmonique devient celui de N. L'endpoint de (54) est conservé. L'audit écrit donne 1<=S(N)<10sqrt(u) et W_kernel=-S(N)+delta, |delta|<=epsilon_W au seuil source u>=10^24. Les premiers rough et les semipremiers rough ont alors des contributions négatives. Leurs comptes ne sont pas minorés par hypothèse.

La forme U7 garde, entre autres,

    B_prime^a <= B_J0+B_J1,c>1+H2-S(N)M2
                  -(u/2)Theta_prime-(3/4)Theta_2
                  +E_corner+N*G54.

Sa forme plus précise conserve la vraie masse -R_pair, sans supposer une minoration de paires premières. J_c compte p, q et N-c*p*q premiers, avec p<q canonique. Le cofacteur c est court mais son poids garde trois conditions premières. H2-S(N)M2, J0 et J1,c>1 demeurent sans estimation indépendante.

Deux coûts nouveaux sont payés dans les preuves écrites auditées :

| Coût | Borne positive | Domaine et limite |
| --- | --- | --- |
| Une seule union de coins n<=Q ou m<M | E_corner=30N^(3/4)u^3 | <N/(1024u logu) dès u>=65536 ; <10^(-12)N/(u logu) au seuil source |
| Mobilité de S(nN), sur les n distincts et unitaires | abs(R_sing)<=3u(1+u)^2 | <10^(-12)N/(u logu) à u>=10^24 ; le principal S(N) reste présent |

Ces paiements écrits ne sont pas de nouveaux théorèmes analytiques Lean. La convention W_positive=-W_kernel donne le principal +S(nN), avec S(nN)=S(N)(1+1/(n-2)) sur n premier unitaire. Le petit n=3 reste présent. La correction de signe du rapport provisoire E7 est journalisée avant gel. Les extractions E11/E12 conservent leur moment signé et leur complément ; E11 recoupe J1 et ne s'ajoute pas comme un nouveau secteur. Aucun second paiement de mobilité ou de face harmonique n'est créé.

### Rejeu fini et erreurs documentées

À N=100000000, a=3163 et Q=999999, onze points ont un premier axe réellement premier et unitaire. Les deux JSON sont reproduits indépendamment en tous champs et tous octets. Les signes sont établis par intervalles rationnels de logarithmes, sans décision flottante ni état UNRESOLVED. Le banc ne prétend valider ni les paiements asymptotiques, ni D_N, ni l'onset source.

Les huit extensions rejetées conservent leurs témoins : tout J2 favorable ; cofacteur c>a ; grand facteur p<=a ; suppression du garde de Möbius ; fibre J1 incomplète complétée ; ratio singulier non-unitaire ; ratio étendu aux puissances propres ; représentation dupliquée. En particulier m=3*3167*3169 avec n=69891331 premier a un coefficient positif ; c=3183>a garde un préfixe incomplet ; les points non carrés-libres ont leur bracket entier nul. Ce sont des réfutations locales, pas une impossibilité globale des poids.

Quatre essais Lean en erreur sont conservés : import de totient inexistant, réécriture sous lambda, réécriture globale de m modifiant m/k, puis simplification du masque sans progrès. Ils ont été corrigés avant la reconstruction finale. Le sorryAx automatique des logs rejetés n'est présent ni dans les sources finales ni dans les sorties réussies. Le blocage de parité est l'absence d'estimation signée restante, pas ces défauts techniques.

### Conservation et prochain contrat

Le Juge confirme 341 artefacts antérieurs intacts, dont les 34 de round9, plus les PDF et ZIP d'origine. Root a lié toutes les empreintes finales et vérifié les 385 entrées du snapshot de production sans relancer les bancs passés ni Lean après leur réussite. Les helpers archivés gardent leur portée historique ; celui de round10 exclut les futures roundNN selon leur numéro parsé. Les pixels source54 restent inchangés : exposant littéral -sqrt(u/60), majorant affaibli utilisé -sqrt(u)/60.

Le ledger retenu reste

    D_N = B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}
            +I_alpha+2max(e,0).

Restent ouverts la compensation de J0/J1 et H2-S(N)M2 avec les masses favorables, ou une compensation indépendante E11/E12 avec son complément ; le seuil effectif BV supplémentaire de la bande physique ; le terme couvert. I_alpha, les proper powers et la face sont comptés une fois. La boucle suivante cherchera une estimation sur les poids réellement couplés en conservant le préfixe bas ; aucune petitesse manquante ne sera ajoutée comme hypothèse d'un certificat.

Documents finaux : round10/agent5.md, round10/judge/judge_receipt.json, round10/controller_manifest.json et .arbor/sessions/parity/.coordinator/messages/round10_feedback.md.

Commande du rejeu final, déjà passée :

~~~powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round10\judge\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
~~~

## Boucle 11 : coefficients lcm et appariement réel avec faces

**Contrôle indépendant réussi ; victoire fausse.** Le Juge a gelé 51 fichiers finaux, rejoué les trois nouvelles banques en tous champs et tous octets, puis reconstruit la dépendance nécessaire et les deux modules dans un dossier neuf. Les trois codes de sortie Lean sont zéro, sans avertissement. Les 28 nouveaux théorèmes portent le cumul à treize modules et169 conclusions auxiliaires distinctes. Les17 théorèmes de la dépendance10 sont reconstruits sans être recomptés ; quinze définitions du module d'appariement sont également auditées, sans accroître le compteur de conclusions.

| Module | Nouveaux théorèmes | Portée exacte |
| --- | ---: | --- |
| round11/lean/SquarefreeLcmCoefficient.lean | 9 | Vrais Möbius/totient/lcm, coefficient rationnel fini pour P carré-libre et r divisant P, wrapper conservant les unités N |
| round11/lean/ThreeAdicPrimePairing.lean | 19 | U2 raccordée au vrai bracket physique J2 ; P1 locale et somme entière avec deux W/incidences et faces J2 ; P2 du vrai principal avec entropie, célibataires et faces |

Tous les axiomes imprimés sont dans propext, Classical.choice et Quot.sound ; bulkCap n'a aucun axiome. Aucun sorry/admit, axiome supplémentaire ou native_decide n'apparaît dans le code exécutable. Les certificats ne prennent pas la petitesse du moment à prouver comme hypothèse.

### Coefficient carré-libre, préfixe et moment bilatéral

Pour P carré-libre et r divisant P, B6 prouve exactement

    sum_{d|P} mu(d)/phi(lcm(r,d^2))
      = (1/r) prod_{p|P,p ne divisant pas r}(1-1/[p(p-1)]).

Le wrapper conserve les unités dans les deux axes. Le coefficient infini, les queues B8/B9 et l'erreur AP ne sont pas déduits de cette seule identité finie. Le raccord écrit conserve les intersections lcm(r,d²), les poids fixes avant AP, les puissances propres de Lambda_N et le principal source S(N)N. Il redonne la référence acquise au §6 ; aucune compensation de parité nouvelle n'en est inférée.

Le vrai détecteur bilatéral est G_N(m)=mu(m)^2 Lambda(m)+S(N)mu(m). Le garde carré-libre évite de réintroduire les puissances propres du second axe. Le témoin m=483 avec N-m premier donne G_N/S(N)=-1 et réfute le faux minorant pointwise avant Lean. La minoration bilatérale B13 reste ouverte. U_a contient tout r<=a, y compris r<=alpha : la bande acquise n'est pas un paiement du préfixe bas.

### Appariement réel et paiement commun partiel

Dans J2, m=c*p*q, c court carré-libre, p<q premiers>a, U2 prouve U_a(m)=-Lambda(c), mu(m)=mu(c), Lambda(m)=0, puis raccorde le bracket à theta(N,n)[Lambda(c)+mu(c)W]. Le Q d'origine, le front strict et les unités n*N restent littéraux.

Pour 3 premier à N, la grille canonique X de c se partitionne en D,3D etF, de façon disjointe et injective. P1 conserve les deux incidences premières, les deux noyaux W distincts et les valeurs réelles des faces. P2 prouve

    K2 = H2+S(N)(Delta_common+Delta_single+Delta_face).

Le certificat porte sur chaque p<q canonique et sa somme finie réelle ; il ne fournit aucune borne sur ces trois composantes. S(N) est défini par le produit source, sans nouvelle preuve Lean de convergence ou de majoration de ce produit. Le raccord quantitatif de P1 à P2 utilise seulement l'input écrit (54), sur les points premiers bulk.

Les deux audits indépendants valident le paiement écrit P5 du seul modèle commun :

    E_common = (9/2) C_sieve S(N)^2 N/u^2+2S(N)sqrt(N),
    C_sieve = 134217728/2541.

Les racines de n(3n-2N) donnent le masque3N et S(3N)=2S(N). Le crible source garde le défaut CRT +1, son reste z^4 et son minorant G uniforme. Les couches Q<n3<=Y conservent log(N/n3). Avec S(N)<3ell acquis, E_common<10^(-12)N/(u ell) pour u>=10^24. P5 remplace P4 central : les deux budgets ne s'ajoutent pas. Ce paiement est écrit sous les inputs source, sans certificat analytique Lean et sans validation asymptotique par N=10^8.

Le signe favorable -S(N)A_common,+ reste présent. Le crédit rough c=1 est déjà dans K2, et l'erreur harmonique de tout J2 n'est facturée qu'une fois. Pour 3 divisant N, cette extraction n'est pas utilisée. H2, les célibataires, les faces, J0 et J1,c>1 restent sans compensation indépendante.

### Numérique, tentatives rejetées et conservation

Les trois banques neuves à N=100000000 comprennent seize r divisant P=3003, douze expansions tête/queue AP sur un ensemble restreint de cinq vrais premiers, et deux partitions finies X={1,3,7}=D union3D unionF. Elles conservent les puissances propres raw, dont n=9, sans masque mu(n)^2.

Le Juge vérifie treize ERROR_FALSIFIER locaux et quinze certificats de signe rationnels stricts. La paire d=1,p3167,q3169 a un modèle conjoint négatif et une somme entière positive par l'entropie. Le singleton avec q3191 et la face d=7 ont des contributions positives conservées. Le banc n'a aucune base conjointe mu(d)<0 : il ne valide pas le coût asymptotique P5. Aucun D_N global ni no-go universel n'est estimé.

Trois essais Lean ont réellement échoué avant correction : un rôle3 sur une simplification sous lambda, deux rôle4 sur la coprimalité/l'inférence/factorisation de sommes puis l'arithmétique Nat.sub. Tous leurs logs et snapshots sont gardés. Le KeyError de préflight4 précède Lean et est classé séparément. Les sorryAx automatiques des sorties rejetées ne contaminent aucun certificat final. Le défaut mathématique restant est une absence d'estimation signée, distincte de ces erreurs techniques.

Le Juge confirme les405 artefacts antérieurs intacts avant et après exécution, dont les64 finaux10, ainsi que les PDF/ZIP d'origine et les pixels source. Root lie les sources et reçus finaux par empreintes, sans aucun rejeu de tests. Le manifeste de contrôle est round11/controller_manifest.json ; le reçu indépendant est round11/judge/judge_receipt.json.

Le ledger reste D_N=B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}+I_alpha+2max(e,0), a=ceil(N^(7/16)), Q original. I, les properpowers et la face harmonique gardent leur paiement unique. Restent ouverts la compensation réelle H2+S Delta_single+S Delta_face avec J0/J1 et les vraies masses favorables, ou la minoration bilatérale B13 ; le seuil effectif BV supplémentaire ; le terme couvert. Le retour de recherche est .arbor/sessions/parity/.coordinator/messages/round11_feedback.md. La recherche reste active et la cible N/(256u ell) n'est pas démontrée.

## Boucle 12 : capacité fermée et transfert normalisé sans estimation

**Audit indépendant passé ; condition de victoire insatisfaite.** Les trois rapports et20 inputs ont été gelés. Les13 bindings numériques et les trois copies isolées concordent sur tous les champs JSON et tous les octets. Le Juge vérifie dix ERROR_FALSIFIER précis et treize positions de certificat de signe strict, dont certaines reprennent le même résultat dans un sous-rapport. Ce compte de positions ne crée aucun nouveau résultat mathématique. Aucun producteur n'est relancé par le Juge ou le coordinateur après le rejeu réussi du rôle6.

Aucun candidat quantitatif n'a franchi la sélection. Lean n'est pas appelé en12 : zéro nouveau module, zéro nouvelle conclusion, cumul13 modules/169 énoncés auxiliaires. Aucun message de compilateur fictif n'est présenté comme échec de parité. Les identités exactes ci-dessous ne sont pas compilées comme substitut à l'estimation manquante.

### Deux promotions réfutées et une direction ouverte

Dans le graphe de suppression de premiers conservant m/p>=M, M=ceil(N^(3/4)), toute arête vérifie p< a sous aM>N-2. Le noyau des facteurs premiers>a est invariant. À N=100000000, t=3167*3169 a le cofacteur bulk complet X={1,3,7}, trois vrais premiers complémentaires et un défaut entier strictement positif avec ses trois kernels W réels. Son modèle est positif pour tout S>0 : log3 logn3+log7 logn7+S(logn3+logn7-logn1). La capacité locale dans chaque composant bulk est donc une fausse promotion universelle. Les enfants nonbulk, l'entropie et la face terminale restent présents ; aucun budget de corner ne paie leur multiplicité gratuitement. Cela ne réfute pas un nouvel opérateur traversant les noyaux ou une estimation limitée au seuil source.

Le détecteur E=mu+mu²Lambda/logm, m>1, satisfait E=V-P avec V=-sum_(d|m,d>1)mu(d)Lambda(m/d)/logm et P=(1-mu²)Lambda/logm. Il annule premiers et puissances propres du second axe, mais vaut mu sur les composites carré-libres. La couverture absolue complète sum_(p|m)logp/logm=1 réfute le gain gratuit1/logm. Le nouveau m=17³ avec N-m premier impose V=P=1/3. Le premier axe raw n=8017² reste actif dans Lambda_N, sans filtre mu(n)². La combinaison R_tilt+S(P_even-P_odd)+S Lambda_N(N-1)-S N n'est pas estimée.

Le transfert premier normalisé du vrai G conserve mu(c)Lambda_N(N-pc), logp/logpc, c=1 et tout c>a. Son modèle apparié est S(cN) sous le garde d'unité ; le test local ne calcule pas un produit infini ni une densité première. La dispersion conserve DD-DM-MD+MM ; sa branche première possède les trois formes p,N-cp,N-c'p, les collisions Ncc'(c-c'), les diagonales, masques et CRT+1. Les branches à puissances propres persistent. BV ordinaire ne fournit pas une estimation indépendante de cette variance centrée ni du modèle signé. Cette piste est **non estimée**, et n'est pas déclarée mathématiquement fausse.

Le polynôme de la seule sélection E={29,561} est Az+Bz³, A,B>0, avec défaut de log-concavité -AB. Il réfute la promotion sur toute sélection physique seulement ; aucune propriété du polynôme global n'en est déduite.

### Domaine, conservation et pièces définitives

Les témoins N=10^8 sont hors du domaine source u>=10^24. Les réfutations universelles finies, l'identité structurelle du graphe et une éventuelle estimation asymptotique ont des portées distinctes. Aucun no-go global n'est allégué. Les487 artefacts antérieurs, dont82 définitifs11, et les PDF/ZIP d'origine sont préservés. Le coordinateur vérifie toutes les liaisons finales sans refaire les tests ; son manifeste lie26 fichiers12 et porte SHA d84cca25948c6794764f3afbc7b6fa23d46faa4152fdad17f2f87da69929a400.

Les trois probes sont enregistrés dans l'arbre :13.2 capacité bulk locale,1.2 gain absolu inverse-log,11.3 transfert/dispersion. Les deux promotions fausses sont taillées dans leur portée précise ; le transfert non estimé reste disponible. Le ledger source reste D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0). Les charges déjà acquises ne s'ajoutent pas deux fois. H2/célibataires/faces/J0/J1 avec les vraies masses favorables, ou le moment bilatéral et son principal, le seuil effectif BV supplémentaire et le terme couvert demeurent ouverts.

Pièces : [rapport du Juge12](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round12/agent5.md), [reçu indépendant](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round12/juge/judge_receipt.json), [manifeste root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round12/controller_manifest.json), [rapport numérique](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round12/agent6.md).

La recherche reste active. Le prochain contrat devra établir une estimation indépendante de compensation entre noyaux de grands facteurs avec son complément nonbulk, ou du moment centré réel à trois formes. Une nouvelle identité standard, une capacité postulée ou une borne sur les seuls petits coûts ne suffisent pas.

## Boucle 13 : échange réel entre J2 et J1, coût sur les couples admissibles

**Contrôle indépendant passé ; condition de victoire insatisfaite.** Après gel de64 fichiers et des cinq rapports, le Juge reconstruit séquentiellement les deux dépendances nécessaires puis les deux modules neufs dans un dossier neuf. Les quatre codes Lean sont zéro, sans avertissement. Les36 théorèmes historiques reconstruits ne sont pas recomptés ; les39 conclusions nouvelles portent le cumul à15 modules208 auxiliaires. Les définitions utilisées ont leur audit d'axiomes, limité à propext, Classical.choice et Quot.sound ; sourceFront n'utilise aucun axiome. Aucune preuve incomplète, axiome supplémentaire ou décision native n'est accepté.

| Module | Théorèmes nouveaux | Portée |
| --- | ---: | --- |
| round13/lean/PrimeSemiprimeSwitch.lean | 23 | Six vrais diviseurs courts de l'image, préfixes opposés, vrais mu/Lambda, coefficients du sourceBracket, déplacement, canonicalités parent/image et disjonction |
| round13/lean/HarmonicKernelVariation.lean | 16 | Vrai harmonicKernel, masqueN pour premiers>Q, front strict/cap original, identité tête/queue et borne absolue finie par vrais coefficients mu/phi |

### Coefficients réels et variation conservée

Le candidat13.3 traverse les grands noyaux : p devient p-2=r*s, le parent J2 m0=c*p*q devient l'image J1 incomplète m1=c*r*s*q. Sous c<r<s<=a<p<q, cr,cs<=a<rs et crs>a, les diviseurs courts sont {1,c} et {1,c,r,s,cr,cs}. Leurs vrais préfixes sont -logc et +logc ; mu vaut -1 et+1, Lambda vaut zéro. Sur les deux vrais premiers complémentaires, avec toutes les unités et gardes bulk/Q,

    B_pair=-(logc-W0)log(n1/n0)+log(n1)(W1-W0), n1=n0+2cq.

Le théorème dérive ces coefficients du bracket physique entier ; aucune égalité W0=W1 ou capacité n'est supposée. Les facteurs ordonnés récupèrent réellement chaque parent et chaque image ; leurs signes mu les rendent disjoints. Cette unicité ne fournit aucune existence de partenaire premier.

Avec R_i=min(Q,floor((m_i-1)/a)), la variation compilée est

    W1-W0=log(m0/m1) A_N(R1)
          -sum_(R1<k<=R0,(k,N)=1) mu(k)/phi(k) log(k/m0).

Le cap Q source, k1, le front strict et toute la queue sont gardés. Une borne absolue finie par les sommes de1/phi(k) est également compilée, sans targethyp. La comparaison élémentaire phi(k)^2>=k/2, les floors avec+1 et le domaine bulk donnent la borne **écrite** |W1-W0|<=21u*N^(-1/32), donc coût apparié<=21N^(31/32)u². Les audits indépendants6/4/5 confirment ses gardes et sa comparaison <10^(-12)N/(u ell) dès sourceu>=10^24. Ce paiement en puissance et cette comparaison ne sont pas compilés en Lean. Le signe acquis U4 rend l'entropie favorable au source, mais ni le cardinal K ni la couverture ne sont minorés.

### Falsifiers, erreurs et conservation

Les deux banques nouvelles à N=10^8 et leurs copies isolées concordent sur tous les octets et champs. Le Juge contrôle onze liaisons numériques, huit falsifiers locaux et17 positions de certificat rationnel strict, zérofloat. Le coût asymptotique n'est pas testé par ce N hors du domaine source. La paire descendante réelle a un principal négatif mais une somme positive, donc le commutateur ne peut être effacé ; sa queue possède deux termes unitaires non nuls. Un parent n'a pas d'image première, et la direction ascendante renverse le signe principal. Les opérateurs13 réfutent seulement les faux transferts génériques de commutateur/symétrisation/positivité et le remplacement du premier axe raw sur une arête longue. Aucun no-go global n'est allégué.

Quatre tentatives Lean ont réellement échoué avant réparation : trois rôle3 sur diviseurs exclus, non-nullités/distinction des facteurs, noms de lemmes et récupération du facteur p ; une rôle4 sur masque coprime, paramètreN, division positive et inégalité triangulaire. Chaque source/log échoué est conservé. Ces diagnostics techniques sont distincts de l'estimation signée manquante. Les sorryAx automatiques des sorties rejetées n'apparaissent dans aucune source ni sortie finale acceptée.

Le Juge confirme les514 artefacts antérieurs intacts avant/après, les PDF/ZIP originaux et les dépendances exactes. Il lit les nouveaux reçus numériques déjà rejoués sans relancer aucun producteur. Root lie les preuves, sorties fraîches et reçus par empreintes sans test supplémentaire. Pièces : [rapport indépendant13](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round13/agent5.md), [reçu](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round13/judge/judge_receipt.json), [manifeste root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round13/controller_manifest.json).

### Obligations restantes

Le complément exact reste B_J0+B_(J1 privé de T)+B_(J2 privé de P). P5 porte sur K2 J2 bulk **entier**, avant retrait exact des parents et de leurs erreurs ; NG54 n'est pas facturé une deuxième fois sur les sommets appariés. Entropie/célibataires/faces/nonbulk, principal bilatéral avec c1 et -S(N)N/long, seuil BV effectif supplémentaire et terme couvert restent ouverts. Le ledger unique D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0) conserve tous ses frais acquis une fois. La cible N/(256u ell) n'est pas démontrée.

## Boucle 14 : déficits exacts et capacités élargies, comparaison non estimée

**Audit indépendant exit0 ; victoire fausse.** Les trois rapports finaux et37 fichiers de production sont gelés. Le Juge vérifie32 liaisons numériques, les deux copies isolées sur tous les champs et tous les octets, sept paires stockées et78 vertices physiques distincts, dont44 arêtes élargies. Aucun producteur PASS, ancien banc, Lean ou rendu PDF n'est relancé par lui ou par root. Le cumul reste15 modules/208 auxiliaires. L'absence d'estimation quantitative n'est pas présentée comme un message d'erreur Lean.

### Deux déficits conservés et comparaison indépendante du matching

La famille p vers p-2h, 1<=h<=H=ceil(N^(1/64)), a des degrés parent et image au plusH. La charge normalisée1/H garde exactement la somme des paires et les deux déficits, y compris les vertices de degré zéro. L'injection13 à h fixé n'est pas une injection sur toute l'union des déplacements.

Le graphe de toutes les descentes t=rs<p dans chaque bloc(c,q) a des voisinages emboîtés. La récurrence D_j=max(D_previous,j-T_j) calcule son défaut de matching, sans Hall postulé. Sa partition entière conserve les parents non servis et les images non utilisées. Le principal pondéré C16 est cependant exactement

    (logc+S(N)) [sum_P log(N-cqp)-sum_T log(N-cqt)],

indépendant du matching. Les images tardives peuvent donc participer à une autre compensation pondérée. Un déficit injectif descendant ne réfute pas cette voie ; un seul cardinal final ne prouve pas non plus la couverture des préfixes.

La comparaison C17 entre p,N-cqp premiers et rs,N-cqrs avec leurs deux caps r,s<=a/c demeure non estimée. Le conducteur cq peut atteindre N^(9/16) ; aucun cq<=sqrtN, densité première, crible de Chen adapté ou BV suffisant n'est acquis.

Les audits confirment deux coûts **écrits**, sans nouveau certificat analytique Lean :42N^(63/64)u² sur les seules paires normalisées et28N^(37/64)u³(1+u) sur le front entier a<p<=a+2H de la seule sous-famille c premier. Le front est compté une fois ; la borne utilise la somme acquise des1/phi(k)<=3(1+u). Chacun est inférieur à10^(-12)N/(u ell) au sourceu>=10^24, mais ils ne paient pas la masse intérieure. La route U4 de tous les vertices sélectionnés, coût epsilon_W N u, peut remplacer la petite variation ; elle ne s'ajoute pas à celle-ci ou à un second NG54.

### Contrôles nouveaux à N=10^8

Le bloc neuf c3,q3581 examine tous les417 entiers3164..3580 et conserve12 parents/11 images. La fenêtre H2 a une arête. Le graphe élargi a37 arêtes, matching7, déficit5 ; après retrait du seul parent de front3167, l'intérieur a11 parents, matching7, déficit4. Les quatre images tardives inutilisées restent dans le bilan. Les sept paires uniques ont un principal formel négatif mais six sommes réelles positives et une négative : le commutateur n'est pas effacé.

Les facteurs interdits des cuts CRT contrôlent seulement les petits déplacements. C1 fixe c7,p=104mod105 et2/4/6 sur p ; C2 fixe p,q=32mod35 et2/4 sur les deux axes. Leurs fenêtres complètes donnent respectivement10 parents/21 images élargies et un parent/23 images. Dans les deux sélections, la dette sans petits voisins est positive, la capacité élargie positive, et dette moins capacité négative. Les images sont comptées une seule fois ; les groupes ne sont pas additionnés sans union physique. Ces comparaisons ne prouvent pas Hall pour toutes les sous-sélections ni une compensation globale. La double classe105 est physiquement vide au point testé et ne porte aucune dette inventée.

Quatre promotions universelles finies sont réfutées : couverture H2, couverture injective P_all, couverture du cut C1 par les trois shifts, couverture C2 par H2 sur les deux axes. Elles ne réfutent pas une estimation limitée au domaine source. Les27 positions de signe strict comprennent21 certificats sur les sept paires et six sur les cuts ; ce nombre ne crée pas27 théorèmes.

Une véritable assertion numérique a échoué avant correction :3217/3917 avait été exigé comme parent, mais son complément11793077=73²*2213 est composite, raw Lambda_N nul. Source, snapshot et log sont conservés. Le vrai parent3217/4337 a complément2335097 premier. Cette erreur de sélection n'est ni une fausse identité arithmétique ni un échec Lean.

### Conservation et reprise

Les603 artefacts historiques, dont89 finaux13, et les PDF/ZIP originaux restent inchangés. Root vérifie toutes les empreintes définitives et lie47 fichiers14 ; avec son controller, le gel14 compte48 fichiers. Le controller14 porte SHA6795b8ed10872337ac8d0f7caf7ef428b8611b6f35376e575c22661ff68e30bf. Le prochain registre devra donc protéger651=603+48 fichiers.

Pièces : [rapport indépendant14](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round14/agent5.md), [reçu](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round14/judge/judge_receipt.json), [manifeste root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round14/controller_manifest.json), [rapport numérique](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round14/agent6.md).

Les nodes13.4/13.5 sont enregistrés comme mécanismes partiels non estimés, sans tailler les voies valides de comparaison pondérée ou de dual élargi. Le ledger D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0) demeure entier. P5 reste sur tout K2 J2bulk avant retrait exact des principaux et erreurs ; c1, raw properpowers, -S(N)N, modèle S(cN), longs, célibataires/faces/nonbulk, onset BV physique supplémentaire et terme couvert restent ouverts. La recherche active se poursuit en15 vers une information indépendante sur les incidences couplées ou le complément signé ; la cible N/(256u ell) n'est pas démontrée.

## Boucle 15 : covariance du masque et fusion des petits cœurs, estimations ouvertes

Les contraintes sont relues après archivage14 et le contrôle strict passe. Le rôle6 et root confirment le registre exact651 (SHA d43941b27a4325a841282d389476c9c6fa9af920138b9b0deebe1c484a4ff7f4), toutes ses empreintes et son inventaire, sans ancien test. Les48 fichiers finaux14 restent gelés. Les deux mécanismes15 sont sélectionnés sous13.6/13.7 avec prompts archivés ; le Juge indépendant a terminé son audit unique des rapports finaux. Aucun Lean15 ni victoire n'est annoncé.

FINAL1_15 réindexe les images sous le conducteur réel d=cr≤a et conserve un masque semipremier β sans filtrer la première incidence. La projection sur les unités donne une covariance Γ non estimée. La progression entière neuve d141 comporte695035 entiers,278014 unités,60982 vrais premiers complémentaires,4201 éléments du masque et912 images premières. Γ est strictement négative : le remplacement exact du masque par sa densité est réfuté dans cette famille finie. Les49 properpowers raw sont conservées ; seuls cinq nouveaux kernels de raccord sont échantillonnés, sans extrapoler leurs signes. L'unique copie isolée est identique en octets et champs. Un supplément ciblé, lecture seule du gate, vérifie la variance, le gap Cauchy strictement positif et le front AP exact X97999795, correction−35/23 ; il ne recalcule aucun kernel ni producteur PASS. L'estimation BV cumulative conserve K_N et un onset supplémentaire inconnu. Les normes écrites ne paient pas Γ.

FINAL2_15 fusionne les petits cœurs composites complets. Pour une cible E de rang pair≥4 par q, les cœurs parents composites de rang impair≥3 ont le vrai coefficient W, la cible a pour coefficient−W, et le principal est majoré par la masse des cibles sans partenaire. Le cœur e1 et les cœurs premiers sont séparés. Ces gardes ont été corrigées pendant la lecture provisoire avant le gel, sans inventer une erreur Lean. La fenêtre complète q8000..8200 donne21 q,86 labels fusionnés en78 cœurs,1680 vertices,416 vrais profils D/W,360 parents premiers,7 cibles premières et112 arêtes. Les248 parents dont la cible est composite sont retenus. Les sommes entières Δ et B sont négatives ; les paires réelles donnent71 signes négatifs et41 positifs malgré112 principaux négatifs. Aucun orphelin n'apparaît dans cette fenêtre ; la disponibilité au source et la capacité entre plusieurs E ne sont pas démontrées.

Pièces mathématiques finales : [FINAL1](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/agent1_weighted_incidence.md), [FINAL2](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/agent2_signed_cofactors.md). Le cumul15modules/208auxiliaires demeure celui du gel13. Les mécanismes sont partiels et le ledger entier reste ouvert. Objectif actif, aucune entrée utilisateur requise.

### Clôture indépendante15 et poursuite

**Audit indépendant unique exit0 ; victoire fausse.** Les trois rapports et39 productions finales sont gelés. Le Juge vérifie35 liaisons numériques, trois copies isolées identiques en champs/octets et1138 positions rationnelles de signe :1131 certificats et sept intervalles du supplément L4/AP. Ces compteurs ne sont pas de nouveaux théorèmes. Quatre promotions finies sont réfutées ; la disponibilité des partenaires n'a aucun contre-exemple dans la fenêtre et demeure non prouvée universellement. Aucun producteur PASS, ancien banc, Lean, dépendance ou rendu PDF n'est rejoué par le Juge ou root. Il n'y a aucun véritable essai numérique ni Lean échoué en15 ; les deux corrections de domaine sont antérieures au gel.

Les651 archives et PDF/ZIP originaux restent intacts. Root lie49 fichiers15 et son controller constitue le fichier50, SHA7b2522fbeec0c17965b9bfba4df418552f0e31b2b4881c91edff00b79a81869f. Le prochain inventaire protège701=651+50 fichiers. Les nodes13.6/13.7 sont enregistrés done0 avec leurs obligations ouvertes, sans éliminer les mécanismes valides. Le contrôle strict des artefacts est effectué après génération du rapport d'arbre.

Pièces : [Juge15](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/agent5.md), [reçu indépendant](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/judge/judge_receipt.json), [manifeste root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/controller_manifest.json), [rapport numérique](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/agent6.md). La recherche reste active vers l'estimation couplée de Γ ou de F6 après union ; D_N≤N/(256u ell) reste ouvert.

## Reprise active : boucle 16

Après la clôture15, le rapport d'arbre est régénéré et le contrôle strict des artefacts termine exit0/OK. Les contraintes fraîches sont relues. Deux idéateurs sont lancés sur l'estimation pondérée réelle de Γ et sur F6 avec capacité globale après union. Le rôle6 prépare le registre exact701 et ne lancera une banque nouvelle qu'après sélection d'un contrat falsifiable nécessaire. Les50 fichiers finaux15 restent immuables. Les formaliseurs et le Juge interviendront après sélection d'un candidat pertinent ; aucune victoire ou compilation16 n'est annoncée. Recherche active, aucun besoin d'entrée utilisateur.

Le préflight16 puis root confirment indépendamment l'inventaire701 et les49 bindings du controller15, SHA du registre5939d791139dbb3f9b26e5d1f372bbdf98d1927f9aaf2c5e9c22aa0a4e35d043. Aucun ancien test ni Lean n'est relancé. L'idéateur1 étudie un possible drift TypeI local du masque selon les vrais diviseurs du candidat premier ; son modèle corrigé et la voie TypeII ne sont pas encore estimés. Aucun contrat numérique16 n'est sélectionné à ce stade.

### Sélection16 et premier résultat nouveau observé

Les deux mécanismes16 sont sélectionnés sous13.8 et14.1 après lecture entière des rapports et contraintes fraîches. FINAL1 est gelé SHA f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754 ; FINAL2 SHA f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b. Le rôle1 dérive un défaut TypeI3 de taille principale pour sa référence uniforme, puis conserve la correction locale et la covariance résiduelle. Le rôle2 donne par écrit la marge S(N)-logp0≥1/144 pour le premier impair minimal absent d'un N pair positif ; son signe source reclassifie une sous-famille existante sans minorer ses incidences. Les formaliseurs3/4 sont lancés sur le vrai produit eulérien et la marge harmonique, sans postuler la marge.

Le banc1 neuf complet d77 passe à son premier essai puis dans son unique copie isolée, identique en octets et champs. Sur129870 entiers, J51948 et β216 avec classes0/106/110 ; le drift uniforme38 devient2 après correction, différence36. Les vrais premiers candidats ont les comptes5067/5079/0 ; neuf properpowers raw restent présents. Γ, Γ corrigée et L3 sont strictement négatifs dans cette fenêtre. Aucun kernel D/W ni estimateur source n'est appelé pour cette question locale. Root a lu les nouvelles sources, rapports, logs et reçus, et vérifié leurs empreintes sans lancer le producteur. L'audit indépendant16 reste à faire.

Le second banc sélectionné garde tous les petits cœurs physiques sous leur cap98 et tous qpremiers dans1000100..1000300, avec e1/e3 dépensés une fois. Il est en préparation/exécution par le rôle6, sans résultat présumé. Les champs de conservation issus du préflight sont statiques et ne suivent pas les nouveaux lancements ; les reçus d'exécution font foi pour ceux-ci. Aucun Lean final16 ni victoire n'est annoncé. Γ/TypeII, F6 et capacité globale restent ouverts ; la cible D_N≤N/(256u ell) reste non démontrée.

### Second banc16 et marge harmonique compilée

Le second banc neuf passe à son premier essai et dans son unique copie isolée, identique en octets et champs :18 qpremiers parmi201 entiers,34 cœurs,612 points physiques,128 profils réels D/W. Le déficit principal est positif aux deux endpoints de l'enclosure S(N) ; le déficit réel après seules ressources e1/e3 et la somme réelle entière sont positifs. Aucune properpower raw n'apparaît dans cette fenêtre. La capacité favorable ne suffit donc pas ici à payer le corps entier sélectionné. Cela ne réfute pas le signe source A9 ni un futur contrôle asymptotique. Source/gates/reçus sont gelés, le Juge indépendant reste à faire ; root a lu la source et les logs et vérifié les empreintes sans rejouer la banque.

Le rôle4 livre un module Lean neuf compilé dès le premier essai :9 théorèmes,0 nouvelle définition,0 warning et uniquement propext/Classical.choice/Quot.sound. La marge harmonique H_(p−1)(p−2)/(p−1)−logp≥1/144 pour p≥13 et les petits logarithmes sont prouvés sans paramètre S libre. Source e1dbd4f8a68b433c4641c90d6eb12366e7084b0d8b7b7b045b8b11ebd41e6b4a, rapport FINAL4 b12adfa9f03ed0af0735278946ebbf09f9bf41e3a6c4d42cc8912ddedb0097b7. Le rôle3 poursuit le raccord au vrai produit singulier et les petits cas ; ces neuf auxiliaires seuls ne prouvent ni A7 entier ni D_N. Le cumul final indépendant16 est en attente de l'audit, aucune victoire n'est annoncée.

### Clôture indépendante16 : marge canonique acquise, incidence globale ouverte

**Deux nouveaux modules Lean recompilés par le Juge, sans sorry, erreur ni avertissement. Aucune victoire.** Pour N pair non nul et p0 le vrai premier impair minimal qui ne divise pas N, le théorème `GoldbachRound16.Anchor.canonical_least_missing_prime_margin` établit S(N)-log p0>=1/144 sous la seule enclosure C2 acquise. Le produit infini réel, sa queue et sa relation au produit eulérien/harmonique sont prouvés ; la conclusion n'est pas substituée par une hypothèse. Les petits cas utilisent l'enclosure ; p>=13 n'en dépend pas. A9 et ses gardes source demeurent écrits et non compilés.

La minoration ne donne pas la masse des incidences q,N-p0q premières. Le nouveau banc complet de capacité à N=10^8 conserve tous les34 cœurs sur18q,612 vertices,128 profils et484 zéros exacts :95 incidences, zéro e1 et trois e3. Le déficit principal entier aux deux endpoints et la somme réelle entière sont positifs. Le centrage TypeI3 uniforme est réfuté ; la correction conserve son prix exact et ne paie pas Gamma_star/TypeII. Quatre falsifications locales, une promotion sans contre-exemple fini,1879 positions de signes stricts654POS/95NEG/1130ZERO, aucun flottant ni signe irrésolu. Les deux copies isolées existantes sont identiques sans relance.

Neuf vrais exit1 Lean techniques sont archivés avec leur source et leur journal ; aucun diagnostic analytique de parité n'est inventé. Les36 théorèmes nouveaux et huit définitions sont comptés séparément, pour17 modules et244 conclusions auxiliaires. Les cinq FINAL et78 inputs sont gelés,30 bindings numériques vérifiés. Audit unique exit0 et deux nouvelles compilations indépendantes exit0. Les anciens701 fichiers et PDF/ZIP originaux sont conservés ; controller16 lie97 pièces et lui-même, portant le prochain inventaire à799. SHA controller16: 10d9f68fc649d965aa5eecac96fecf5fd20f705527d42f52b855662acec02332. Les nodes13.8/14.1 sont enregistrés done0 ; les deux mécanismes valides sont conservés avec leurs obligations ouvertes.

Les mentions antérieures « en attente » de cette boucle décrivent les observations avant le gel ; tous les rôles16 sont maintenant FINAL. Le problème de dispatch a été résolu avant l'audit. La suite cherche une estimation quantitative de Gamma_star/TypeII ou de la capacité d'incidences après union globale. La cible D_N<=N/(256 logN loglogN) reste non démontrée.

Pièces : [EulerAnchor.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/role3/EulerAnchor.lean), [LeastMissingPrimeMargin.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/role4/LeastMissingPrimeMargin.lean), [Juge16](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/agent5.md), [manifeste root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round16/controller_manifest.json).

## Boucle 17 en cours

Après lecture fraîche des contraintes, deux idéateurs travaillent sur le contrôle quantitatif de la covariance corrigée et de la capacité globale des incidences. Le rôle numérique vérifie l’inventaire exact des 799 archives avant tout nouveau test. A7 est acquis ; aucune hypothèse de densité ou de partenaire premier n’est ajoutée. Aucun nouveau candidat ni essai Lean 17 n’est encore annoncé.

Le préflight 17 et le contrôle indépendant root confirment exactement 799 archives intactes, avec les deux sources originelles. Une piste provisoire du rôle 2 traite une sous-famille par quatre formes affines ; les branches non rugueuses et le coût de l’union restent explicitement ouverts. Les deux idéateurs sont actifs et le rôle numérique attend le candidat sélectionné. Aucun nouveau banc ou compilateur 17 n’a été lancé.

### Sélections 17 et observation du premier banc canonique

Les deux FINAL conceptuels et l’addendum de masque sont figés et sélectionnés sous 14.2 et 13.9. Le masque réel ancien était gcd(b,N) ; la variante avec77 conserve son prix E77. Les deux nouveaux contrats numériques sont autorisés. Les formaliseurs3 et4 travaillent effectivement en parallèle sur les poids Selberg construits et les racines réelles des quatre formes ; chaque essai technique est conservé. Aucun nouveau module complet n’est encore certifié par le Juge.

Le premier banc canonique neuf passe à son premier essai :201 entiers q,9 premiers unitaires,28 cœurs,252 candidats,47 noyaux D/W neufs et205 axes exactement nuls. Il vérifie les poids finis, principale=1/G, les carrés point à point et les vrais restes CRT avec +1. Les branches saturées ne forment pas G. La partition active contient11 cibles A,0 R et18 S ; le déficit après ressources uniques et la somme entière sont positifs. Trois promotions locales sont falsifiées ; aucun estimateur C6/C7/U4 source n’est appliqué à N=10^8. Root a lu les sources/logs/reçus et vérifié les empreintes sans lancer le producteur. Le rejeu isolé unique et l’audit indépendant restent à terminer, ainsi que le nouveau banc TypeII complet. Les bornes C4/C6 restent écrites ; T_A/T_S, les autres modes TypeII et D_N restent ouverts. Aucune victoire.

### Deuxième banc17 : vrai mode TypeII et prix distincts

Le banc TypeII complet passe à la tentative2 après une erreur technique de domaine dans la factorisation auxiliaire de rad(hN), conservée avec source et journal. La correction réunit les facteurs de composantes admissibles et garde le contrat. Sur162338 entiers, β181,12460 candidats premiers et8 properpowers raw sont conservés. Les six masques donnent J0=[64936,43291,39961] et J77=[50599,33732,31136]. Les couples v17/19 et leur intersection323 gardent la multiplicité analytique, sans créer de capacité physique. Les identités de calibration et leurs prix sont vérifiés séparément pour theta, II et II_raw ; les deux prix L13_theta sont strictement négatifs dans cette fenêtre. Aucun BV, D/W ou estimateur asymptotique n’est appliqué. Root a lu source, correction exacte, journaux et reçus puis vérifié les bindings sans lancer le producteur. Le rejeu unique TypeII et le Juge restent pendants.

Le rôle3 annonce un premier PASS intégral à l’essai11 pour l’inversion Selberg, principale=1/G, le support nul, la formule des poids et |lambda|<=1, avec axiomes standards seuls. Il poursuit le raccord aux racines effectives du rôle4. Ce résultat producteur n’est pas encore audité ni ajouté au cumul acquis. Le contrôle strict d’arbre reste pendant pour les rapports et métriques des nodes13.9/14.2 encore running ; aucun score fictif n’est créé.

### Gel des nouveaux modules17 et annexe de moment

Les deux formaliseurs livrent cinq nouveaux modules : Selberg42 théorèmes/23 defs, racines et raccords quantitatifs51 théorèmes/17 defs/1 instance. Les producteurs ont conservé23 vrais exit1 techniques (12+11), sans les interpréter comme une déduction analytique impossible. Les journaux finaux ne contiennent que les axiomes standards et aucun sorry. Root a lu les sources finales, les corrections et journaux, puis vérifié les bindings sans compiler. Le minorant du vrai G garde l'input analytique indépendant de somme logarithmique première et la perte de collisions explicite ; C4 source complet/C6/T_A/T_S/global restent ouverts. Le Juge indépendant reçoit tous les FINAL et prépare son audit unique et cinq compilations fraîches. Aucun cumul acquis nouveau avant son verdict.

L'annexe numérique nouvelle, distincte des33 bindings FINAL6 inchangés, vérifie le moment exact et garde toute la queue105/210 des16 sous-ensembles sur chacun des16 cœurs. Un canonique et un seul rejeu isolé exit0 donnent une copie identique. Ses64 certificats stricts (54POS,10NEG) sont séparés des390 premiers. Six conditions demi-moment sont vraies, dix fausses ; les16 marges de Markov restent positives. Le minorant fini G_P≥Z/2 est observé pour tous16, y compris les dix où sa condition suffisante échoue. Aucune borne source n'est appliquée à N=10^8. Root vérifie les pièces et bornes stockées sans relancer les producteurs ou les signes. La victoire reste fausse.

Le premier audit indépendant17, réellement lancé à20:40:07UTC, sort1 avant tout Lean. Conservation799, gel143, bindings33+15 et454 certificats stricts ont passé. Le contrôleur imposait à tort le drapeau small_factor_exclusion_verified à tous252 candidats ; ce drapeau n'est vrai que lorsque le témoin existe et e≡j modulo son petit premier. La source numérique conservait correctement cette garde et les axes theta/raw. Source, snapshot, journal et reçu du Juge restent figés. Une continuation distincte des étapes restantes est autorisée ; aucun rerun des banques ou des signes, aucun échec analytique de parité inventé et aucun cumul Lean17 encore acquis.

### Clôture indépendante17 : vrai G certifié conditionnellement, paiement global ouvert

**Cinq modules recompilés indépendamment sans sorry, erreur ni avertissement ; aucune victoire.** Ils construisent les racines effectives, les poids Selberg avec vraie Möbius et support SF tronqué, puis dérivent lambda1=1, norme<=1 et principal1/G. La saturation donne la cellule vide. Le moment garde toute la queue ; le raccord de collisions donne actualG>=P(y)^4 L_Delta(y)/2 sous un input analytique indépendant de somme première et des gardes explicites. Les93 théorèmes,40 définitions et une instance sont distincts ;134 print axioms n'utilisent que propext/Classical.choice/Quot.sound. Le cumul est22 modules337 théorèmes auxiliaires. La constante C4 source complète, CRT+1 uniforme Lean, C6, A/S, Gamma et le TypeII entier restent ouverts.

Les deux banques nouvelles àN=10^8 et leurs copies isolées existantes sont identiques. Rough :201 entiers9q28cœurs252candidats,47W conservés205axeszéro, partitionA11/R0/S18,10sat16unsat et17488lignesCRT. TypeII :162338entiers181beta12460theta8rawproperpowers,sixmasquesetprixθ/II/II_raw distincts. L'annexe séparée garde les16sousensembles/105210queues,64signs54POS10NEG et6conditionsvraies10fausses. Les390premierssignes242POS62NEG86ZERO restent séparés. Aucune borne asymptotique source n'est appliquée au N fini ; cibleD_N non prouvée.

Les23exit1Lean des30invocations auteurs sont techniques et archivés ;PASS15warning corrigé demeureconservé. Le Juge a deux véritables échecs pré-Lean de lecture de schéma, puis une reprise exit0 : trois audits1,1,0, cinq nouvelles compilationsPASS chacuneunefois, aucune banque/PASS/ancienmodule/W/signe/PDF relancée. Le drapeau d'exclusion n'est vrai que sous sa garde37cas ; kernel_ref estnull205, C_recipe estabsent205. Le rapport final corrige cette précision sans modifier les preuves d'échec.

Root a lu rapports/sources/journaux/reçus puis vérifié143inputs,33+15bindingsnumériques,52bindingsJuge,134axioms,454positions strictes, cinq copies/compilations et799archives, sans exécuter l'audit. Le controller17 lie197pièces et lui-même, pour997archives au prochain préflight. SHAcontroller17: 5d20d749aa30bcf939e33cd0f1d1efc1049c85634f6054ae79c81890e6d628a4. Nodes13.9/14.2 done0, mécanismes valides conservés avec obligations. Les mentions antérieures pendantes sont des observations chronologiques avant gel. Recherche active ; aucun Win ni NoGo global.

Pièces : [SelbergFourForms.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/role3/SelbergFourForms.lean), [FourFormCollisionLoss.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/role4/FourFormCollisionLoss.lean), [Juge17](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/agent5.md), [controller17](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round17/controller_manifest.json).

## Boucle18 en préparation

Les contraintes ont été relues après la clôture17 :31findings et5directionspruned. Deux idéateurs sont envoyés sur le paiement nonrough A/S et le contrôle TypeII/Gamma entier avec ses prix réels ; le rôle numérique prépare un préflight unique997. Les trois dispatches sont acceptés, leur démarrage effectif reste à constater. Aucun node, banc mathématique ou nouveau théorème18 n’est encore sélectionné. Les fondations et les archives1–17 demeurent acquises et figées ; la recherche reste active, sans victoire.

Le préflight18 a été réellement exécuté une seule fois exit0 à21:02:01UTC : inventaire997=799+198 etoriginaux intacts. Root lit source/log/receipts et vérifie les empreintes/inventaire sans rerun. Le rôle1 confirme que le modechi13 ne contrôle pas toutTypeII/Gammaθ etcherche une estimation indépendante avec prix réels. Les deuxidéations sontactives ; rôle6 attendla sélection. Aucun node/bancmathématique/Lean18 sélectionné.

### Boucle18 : deux mécanismes neufs sélectionnés, contrôles en préparation

Les FINALs conceptuels sont gelés et lus intégralement. Node13.10 : séparation des lignes modulo d, coefficient périodique sur un premier omis et minorant CRT écrit du vrai TypeII ; une obstruction de fibre isolée, sans NoGo global. Le conducteur91 fixe concerne seulement le banc fini ; le source garde un conducteur croissant et le premier11 pour la contradiction annoncée. La dispersion mixte après agrégation reste ouverte. Node14.3 : extraction canonique double-semipremière de ressources nonrough, quatre formes divisées CRT et coût écrit de tous e/témoins. Le budget est obtenu seulement pouru>=10^36 ; le gap depuis10^24 et le complément à quotient composite/T_A restent impayés. Le réciproque m0 a axe p0q et raw nul ; aucun crédit fictif ni ressource doublée.

Deux nouveaux contratsN=10^8 sont autorisés :109890b surd91, tousv11..20 et les masques39/429 portées0/91 ; puis5001entiersq1400100..1405100 et touscœursSFunit>3jusqu'à70. Les références et prixθ/II/IIraw, les properpowers, les factorisations et vertices uniques restent visibles. Aucun résultat numérique n'est présumé. Formal3 écrit la séparation/coefficient/somme réelle ; formal4 reçoit le raccord CRT/division/racines. Les compilations de chaque candidat attendent son PASS numérique canonique inspecté ; Juge indépendant aprèsgel. Les22modules337conclusions vérifiées restent le cumul, aucune nouvelle compilation18 encore rapportée, aucun Win.

### Premier PASS numérique18 : identitéTypeII vérifiée, promotion locale réfutée

Une exécution canonique neuve attempt01 a réellement terminéexit0 le2026-10-02à21:35:41UTC. Le banc complet conserve109890b, beta196 sans filtrepremierj,8441candidatspremiers et9properpowersunitaires,57189colonnesw distinctes sur toutv11..20. E17/19 et les deux classes216/948mod1001 sont construits avanttheta. Les quatre J sont27050,24591,23185,21077 ; les comptes omis sont273/234. R2/R7/R8 et les carrés de calibration sont exacts. Les deux témoins normalisés109200000/541 et936000000/4637 dépassent strictement le budget fini x/log²x. La calibration corrigée donnezéro mais son prixL11 conserve toute la contribution. Deux promotions locales seulement sont falsifiées ; aucune identité arithmétique fausse niNoGo global.

Root a lu source/helper/launcher/log/reçu/markerPREEXEC intégralement puis vérifié les captures/empreintes et98certificatsstockés40POS25NEG33ZERO, sans relancer producteur/signes/Lean. Le gate de compilationrole3 est ouvert après cette inspection. Le bancSS et son gate restent pendants, aucun rejeuTypeII lancé à cette observation. Les fichiershelper/source/launcher de cePASS sont figés ; extensionsSSdistinctes. Les anciennes337conclusionsLean restent le cumul vérifié jusqu'au Juge18. Sourceu>=10^24 jamaisappliqué àN1e8, agrégation/Gamma/D_N ouverts, aucun Win.

Pièces : [TypeII18](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/typeii_checks.py), [reçu canonique](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/role6/typeii_canonical_receipt.json), [inspection root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/.arbor/sessions/parity/.coordinator/messages/round18_typeii_root_observation.json).

### Premier échecLean18 réellement archivé

Le rôle3 a compilé SeparatedTypeII après autorisation root/numericPASS : attempt01exit1, du21:41:18au21:41:42UTC. Root a lu intégralement sourcecapturée/log/reçu/builder et vérifié leursempreintes. Huit diagnostics d'erreur et un avertissement concernent syntaxe localattribute, API Coprime.mul_left absente, normalisationModEq, membershipsFinset et simplificationconditionnelle. La source ne contient aucun sorry/admit/axiomead hoc, mais le logéchoué imprime des sorryAx injectés par Lean après erreurs : aucun nouveau module n'est validé par cette tentative. Échec technique conservé, aucun blocage de parité logique inventé ; auteurcorrige, avis API transmis au secondformaliseur. Le Juge indépendant18 reste ultérieur.

### Double extraction18 : calcul canonique contrôlé

SS attempt01 exit1 conserve une erreur d’encodage generator→len ; attempt02 exit0 corrige uniquement cet appel vers une liste. Sources/helpers/launcher/captures/logs/reçus intégralement lus et liés par empreintes par root, certificats rationnels stockés contrôlés sans recalcul des producteurs. Fenêtre5001entiers,333qpremiers,22cores,7326axes : A258/R32/S674, dontSS40 et634horsSS ;286triplets divisés,68sommetsphysiques/54kernelsactifs/14zéros,2ancresdéjàprésentes. Les quatre falsificateurs sont locaux, la borne source D5/D10/D11 n’est pas appliquée au N fini. Le gate de compilation rôle4 est ouvert ; le Juge indépendant et les rejeux isolés restent à effectuer. Aucune victoire ni borne globale D_N.

### Core TypeII18 : PASS auteur, Juge encore attendu

Trois invocations réelles du core : exit1,exit1,exit0. La seconde conserve des erreurs Decidable/elaboration ; la troisième compile sans avertissement ni sorryAx, avec58impressions d’axiomesstandards (30théorèmes,26définitions,2structures). Root lit et lie source/captures/logs/reçus/olean sans compiler. Le core prouve la bijection des vrais couples produit/diviseur, les coefficients périodiques séparés, le coût exact et les prix de calibration. La minoration CRT source et Γ/globalD_N restent ouverts. Aucun nouvel ajout au cumul officiel22modules337aux avant le contrôle indépendant du Juge18.

### FINAL6/18 gelé et Juge indépendant en préparation

Rapport final numérique et67liaisons+manifeste68 ont été intégralement lus et vérifiés par root, ainsi que la clôture après finaliseurmetadataexit0. Trois runs canoniques(0,1,0), deux uniques rejeux isolés(0,0) byteidentiques ;320positionsstockées191POS83NEG46ZERO. Aucun run mathématique/audit/Lean par root. Rôle6 terminé ; Juge18 indépendant nouvellement démarré en préparation seulement. Les FINAL3/4 et l’autorisation d’audit indépendant restent attendus. Cumul officiel22modules337aux inchangé ; déficit globalD_N et victoire ouverts.

### FINAL3/4 gelés : huit modules auxiliaires, contrôle indépendant pendant

Les deux FINALs sont réellement terminés. Root lit les huit sources finales, leurs journaux PASS/FAIL et les rapports/reçus, puis vérifie89liaisons du rôle3,59du rôle4 et18imports historiques en lecture seule, sans exécuter les finaliseurs ni Lean. Les auteurs comptent170nouveaux théorèmes,68définitions,4structures et242impressions d’axiomes standards ou sans axiomes. Les23invocations Lean ont15échecs techniques conservés. Count garde un unique avertissement push_cast bénin ; les autres PASS sont sans avertissement. Une erreur réelle du lecteur de clôture rôle3, qui omettait5impressions sans axiomes, est conservée avec sa capture POSTEXEC déclarée comme telle ; sa correction n’a relancé aucun compilateur.

Le nouveau compte CRT dérive delta(H)=phi(H)/H, les erreurs de bord et l’inclusion-exclusion sur les vrais diviseurs. R5 minore la vraie somme TypeII sous trois gardes indépendantes de longueur/densité ; leurs estimations source et R6 restent non formalisées. Le raccord Selberg utilise les racines réelles du polynôme divisé et prouve G>=P(y)^4*L_actualDelta(y)/2 sous l’input prime-log indépendant ; D5/D10/D11, les demandes horsSS, T_A et Gamma demeurent ouverts. Une annexe rationnelle CRT distincte est en préparation pour tester les fronts et gardes àN1e8, sans modifier FINAL6. Une revue indépendante du contenu est aussi démarrée, sans compilation ni nouvelle hypothèse. Le Juge prépare sa compilation fraîche des huit modules ; aucun audit encore autorisé. Le cumul officiel22/337 reste inchangé, aucun Win.

### Clôture indépendante18 : huit modules valides, contournement global non établi

Le Juge a recompilé les huit nouveaux fichiers Lean, chacun une fois, sans sorry ni erreur. Les170 théorèmes,68 définitions et4 structures ont242 prints d'axiomes vérifiés ; seul Count comporte le warning prévu d'une tactique push_cast inactive. Le cumul atteint30 modules et507 théorèmes auxiliaires. L'audit unique s'est achevé à23:02:52UTC avec exit0, puis sa clôture metadata avec exit0. Aucun stage PASS, ancienne compilation ou producteur numérique n'a été relancé.

Les identités TypeII portent sur les produits et incidences réels ; leur calibration conserve le prix entier. L'inclusion Möbius et les fronts CRT dérivent le minorant R5 sous des gardes arithmétiques indépendantes. L'annexe vérifie1944 cas : J23185/JR234, deux gardes suffisantes fausses, donc aucune application R5 au N fini. Le passage source R4/R6, la non-vacuité structurelle, l'estimation de Gamma entière et ses prix restent ouverts.

La double extraction SS construit les quotients, les quatre formes divisées, leur discriminant arithmétique, les racines effectives et les poids Selberg. Son minorant de G reste conditionnel à un input analytique indépendant. Les fronts source, la conversion Mertens/totient, CRT+1 uniforme et la sommation de tous les paramètres D5/D10/D11 ne sont pas certifiés. Le seuil SS écrit10^36 laisse un segment au-delà du seuil source10^24 ; S hors SS, T_A et l'assignation unique des capacités restent impayés. Le ledger global de D_N n'est pas fermé ; aucune victoire.

Les banques complètes à N=10^8 sont figées : TypeII109890entiers et57189produits ; SS5001entiers/333premiers/22cœurs/7326axes, A258/R32/S674=SS40+634,286switches divisés et68sommets54actifs14zéro. Les320 positions de certificat (191 positives,83 négatives,46 nulles) sont conservées. L'annexe CRT a une invocation canonique et zéro rejeu. Les15 échecs Lean auteurs sont des diagnostics techniques conservés, sans obstruction logique de parité inventée.

La racine a lu les rapports/sources/journaux/reçus et vérifié267 inputs,22 dépendances,91 pièces du Juge,10 bindings de clôture,242 axiomes et997 archives ; son contrôle reste limité aux métadonnées et certificats stockés. Le controller18 lie363 pièces et lui-même ;1361 archives sont protégées pour la suite. SHAcontroller18 : ce00517b1df6f4fc89f27667be44dd7f2c4d3331c8022fd14e4c505392175c5c. Nodes13.10/14.3 done0 ; les résultats auxiliaires restent acquis. La prochaine idéation doit viser une estimation quantitative entière ou une famille encore non couverte.

Pièces : [TypeII et gardes R5](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/role3/SeparatedTypeIILower.lean), [switch divisé Selberg](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/role4/DividedSelbergBridge.lean), [rapport du Juge18](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/agent5.md), [controller18](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round18/controller_manifest.json).


### Clôture19 et recherche20

FINAL19 closed: one actual independent audit exit0 at01:36:25UTC,11fresh Lean PASS,185thm78defs3structures268standardprints/3benignUnitLosswarnings; cumul41modules692aux,noWin. Both new N1e8banks uniquePASS0replay,973nonSS+48308rank storedcertificatepositions only. Authors29actualLean18technicalFAIL and1preLeanPythonparseFAIL, no JudgeFAIL/continuation. All1361archives and307frozeninputs/26historicaldeps/145Judgeownedbindings verified; controller19 binds446+self447, next1808, SHA299a605efaa7cf6721e3b65bfea8af976bcbfcdbb1bc841eee6f4a0d9d9d4d08. True weighted calibration price and allrank nonSS reindex retain every term; GammaRank compensates negativeprincipal, ordinary AP/K14/K18/BV/mediumlong/capacity/parents/supportbridge/e1p0/singletons/fullledger unpaid. Sourceu>=1e24, writtenlocal1e40 notsubstitute. Root onlymetadata/storedhashes+labels read, no proof/compiler/producer/audit/logsign execution.


Independent FINAL19 six calibration modules prove actual rank3 face exclusion, remaining P/gcd(P,d), all overlaps/empty A0, normalized whole prices Gamma0=GammaRank+Pi, actual large-unit losses with +1, squarefree module reconstruction/multiplicity32 in one expansion, seven totient chi and true IE/estimator around -Mchi with literal normalization/AP remainders. All514fibres and8,868,261axes/28,136physicalimages retained, sourceR2/test17 separate, X=d(L-1)+1. Negative Pi is compensated by GammaRank; principal sign alone cannot pay physical incidence. Paper K14/Mpositivity is guarded but not Lean-certified; ordinary AP bridge/combined40/K18/BV onset/whole GammaRank/parents/allledger remain open. Valid auxiliary results, score0, no parityWin.

Independent FINAL19 five resource modules prove largest-real-prime extraction at all ranks including repeats, canonical coprimalities from cap/anchor, D/P tags with equalityD, C<N not sqrtN, signed integer CRT with inverse selectors, actual imported theta/raw bracket reindex on composite StructuralSupport, literal short/medium/long, unique physicalproduct and genuine mu0/m0 zeros, exact cofactorOmega1/2 harmonic identity including p²/converse. Finite1001q/22022axes/5120labels/124demands and220physicalunion/48m1 kept once. Source support bridge e1/p0/singletons/parents, composite rho/H7/H9, allparameter costs, sourcegap1e24..1e40, medium/long/ranks>=4/capacity/T_A/fullledger unpaid. Score0, no parityWin.


Next20: obtain a genuinely new quantitative incidence bound keeping q primality and actual least-factor composite subtraction, or pay an actual exceptional cofactor layer with every +1 and unique reciprocal before addressing its complement. Do not rederive19calibration/bijections/IE/32counts/H8 or promote a favorable price to wholeGamma. Preserve all1808archives/acquis/sourceu>=1e24/fullledger. Fresh constraints and unique conservation required before new selection/banks; no target-equivalent/availability/smallGamma premise or finiteonsetpromotion.


### Clôture20 et recherche21

FINAL20 closed: actual unique independent audit 04:42:00..04:52:05UTC exit0,16freshLeanPASS/0FAIL,250thm83defs1structure334standardprints13benignwarnings; cumulative57modules942auxiliarythms. Authors38actualLean16PASS22technicalFAIL, two new N1e8banks uniquePASS0replay/sourceguardsfalse. True sourcefriable cost<=N/(8192uell) from sourceu>=1e24, no full ledger/parity Win. All2837uniqueJudgeinputs/189Judgefinalbindings/1808previous unchanged;1219roundfiles+self1220next3028, controllerSHA815d2ce77851a01d9addfa4202a17edb787a42f7f080d4e41cab18aa7b002b04. Root bytes/receipts/storedlabels only, zero proof/compiler/audit/producer/logsign execution. 

Independent FINAL20 six composite modules prove actual odd Bonferroni/minFac lower weights, constructed Selberg lambda1/G, physical q-prime composite subtraction with proper powers, exact conductor p*lcm(h,K/gcd(K,p)), nonunits/caps/fronts and signed actual AP remainders=mass-main; full identity retains Tail/Slack. Source B6 variation/window bijection, SD/effective BV, principal source comparison, weighted kappa aggregation and literal M0 bridge remain unproved. Five finite Gamma theta/raw NEG accompany five principal-minus-M0 POS; source guards false, no sign transfer. 91 new thms/50defs/141 standard prints, 14 author Lean actuals/8 technical FAIL; fresh independent Judge six PASS. Score0, no parity bypass.

Independent FINAL20 ten friable modules including source geometry derive repeated-prime prefix, actual Euler/Rankin/tau/TK, two AP +1 fronts, all-rank demand aggregation and unique F1 reciprocal images. Source onset logN>=10^24 alone derives guards/floors/ceils and sourceFriableAbsoluteCost on H19 intersect (F0 union F1) plus unique F1 reciprocal ABS <=N/(8192 logN loglogN). No free small sum or capacity premise. F0 minus F1 nonfriable reciprocal, both-nonfriable complement, H19 whole-source bridge/cross-partition/capacities/parents/Gamma/TA/fullledger remain open; aggregated budget theta, raw envelopes local. 159 newthms/33defs/1structure/193prints,24actualauthorLean14technicalFAIL; independent ten freshPASS. Score0, no parity bypass.

Next21: new quantitative information on actual composite prime incidence/distribution, or cover remaining nonfriable reciprocal/complement with real unique capacities and source support. Preserve source u>=1e24, literal M0/kappa, q primality, PP, Q/k1/wholeUa/allfronts/full D_N ledger. Do not rederive20 Bonferroni/Selberg/AP identities or friable Euler/TK/sourcebudget; no small SD/Gamma/availability/Hall/target-equivalent assumption. Fresh constraints and unique3028 conservation before new selection/banks; six logical roles in four slots, no parityWin.

Fenêtre finie22, première invocation réelle : exit1 à07:22:16UTC, trois erreurs techniques (API continuité, obligation de réécriture, coercition Int.negSucc), aucun olean. Les21captures et inputs sont inchangés. Noyau auteurPASS conservé ; correction distincte en sources, aucun crédit de parité/globalD_N.

Fenêtre finie22, deuxième invocation réelle : exit1 à07:30:11UTC, une erreur de normalisation Int.negSucc/natAbs restante ;32captures inchangées, zéroolean. Noyau auteurPASS intact ; aucune réfutation analytique. BancΓ distinct réellement démarré à07:28:40UTC,17captures, sans verdict anticipé ni paiementD_N.

BancΓ22 réel : unique essai07:28:40..07:34:55UTC exit0,21cas AUX_PASS et12mutations détectées,43certificats racine,17captures/15bindings inchangés. Les6cas hauteur±100 ne discriminent pas un mutant zéro à la tolérance absolue. Aucun crédit Lean, formuleWeil, chaleur, coefficientN ouD_N sur ce test.

Finite22 revision03 : invocation réelle07:35:44..07:36:07UTC exit0,43 captures inchangées,18 audits standards. Unfold infini final est lu FULL avec25bindings vérifiés ; une compilation distincte est autorisée, sans recompilation Kernel/Finite. Juge indépendant et trace globale restent ouverts ; aucun WIN.

Γ auteur1 : exit1 à07:50:40UTC, six erreurs API/tactiques,8captures/6392inputs inchangés, pas olean. Unfold auteur1 : exit1 à07:51:23UTC, trois erreurs rpow/carré/cast,25captures inchangées, pas olean. Deux révisions SOURCE séparées requises ; aucune réfutation analytique ni victoire. Juge5 prépare indépendamment Kernel/Finite réels PASS. Compteur auteur22 :2PASS/5FAIL techniques, officiel57/942 inchangé.

Unfold22 deuxième invocation réelle :07:57:27..07:57:53UTC exit1,36captures inchangées, deux normalisations rpow/pow et simp restantes ; negSucc corrigé. Zéro olean/infini complet, aucune réfutation analytique. Révision03 SOURCE séparée. Auteur22 :2PASS/6FAIL techniques.

Unfold22 troisième invocation réelle :08:05:00..08:05:26UTC exit1,47captures inchangées, un pattern rpow_natCast absent ; carré et negSucc corrigés. Zéro olean/infini complet, aucune réfutation analytique. Révision04 SOURCE séparée. Auteur22 :2PASS/7FAIL techniques.

Juge22 batch01 réellement clos : deux enfants indépendants exit0,42théorèmes+9définitions/51audits standards,10captures/7112inputs/3089archives inchangés. Officiel59modules/993déclarations auxiliaires ; acquishistoriques57/942 conservés. Ce succès reste Kernel/Finite G0. Unfold etΓ non encore certifiés, trace globale/zéros/coefficientN/D_N ouverts, aucun WIN.

Γ auteur2 : START08:13:37UTC, FIN08:15:13UTC, exit1, une erreur de réécriture ligne202, aucun olean ;13captures/6415inputs/3089archives vérifiés. Révision02 distincte préparée, aucun crédit formelΓ ni verdict de parité. Auteur22 :2PASS/8FAIL techniques ; officiel59modules/993auxiliaires après Juge Kernel/Finite.

Unfold04 auteur : START08:29:04UTC, FIN08:29:29UTC, exit0, vraie somme infinie/intégrale dérivée ;16théorèmes+3définitions/19audits standards rapportés,58captures/inputs et3089archives vérifiés. Juge indépendant encore requis, enveloppe Tail SOURCE. Auteur22 :3PASS/8FAIL techniques. Officiel59modules/993auxiliaires conservé, aucune diffusion globale/coefficientN/D_N/WIN.

Γ3 auteur : START08:32:26UTC, FIN08:34:03UTC, exit0 ; vraie Laplace complexe et borne exponentielleΓ prouvées en auteur,20théorèmes+3définitions/23audits standards rapportés.13captures/6442inputs/3089archives vérifiés. Auteur22 :4PASS/8FAIL techniques. Audit indépendant encore requis ; officiel59/993 conservé, H1/coeffN/D_N/WIN non certifiés.

Tail auteur : START08:35:09UTC, FIN08:35:31UTC, exit0, vraie erreur/enveloppe/continuité jointe dérivées ;11théorèmes+3définitions/14audits standards rapportés,30captures/inputs et3089archives vérifiés. Juge indépendant encore requis. Auteur22 :5PASS/8FAIL techniques. Officiel59modules/993auxiliaires conservé, aucune diffusion globale/coefficientN/D_N/WIN.

H1 contour15.3 sélectionné après probe/quatre mouvements : bundlepapier812bad4e,6artifacts+8inputs vérifiés, ROOTconstraints21c7e1/IDEATEcbf72d. PrécritiqueROLE6 active, aucun calculautorisé. Deuxdroites/Mellin/équationfonctionnelle etArchexact proposé, enveloppecontinuepapier, coût etcertificatsàvérifier. H1formelle/coeffN/D_N/WIN restentouverts. Jugebatch02 prépare séparément3nouveauxmodulesauteurPASS.

Juge22 batch02 clos : trois vrais enfants indépendants exit0,47théorèmes+9définitions/56audits standards,23captures/7214inputs/3089archives et35fichiers batch01 inchangés. Officiel62modules/1049déclarations auxiliaires. Le dépliement G0, sa vraie erreur et Γ/H2 sont certifiés ; H1/trace globale, certificat numérique contour, coefficientN et D_N restent ouverts. Aucun WIN.

H1/15.3 : précritique indépendante sur papier cohérente, manifeste fe767a62 lié ; aucun nouveau calcul ni preuve globale compilée. Le plan DFT conserve tous les nœuds, optimise leurs puissances par récurrences certifiées et sépare quatre budgets. Primitives et contrat exécutables encore en préparation ; coût non mesuré. La trace finie et le passage infini des contours restent distincts. Aucun paiement du coefficient N ou de D_N, aucun WIN.

H1 composantes, tentative01 : exécution réelle 10:06:52–10:10:21 UTC, exit1. Échec technique de sérialisation du rayon E_function (>4300 chiffres), sans résultat complet et sans PASS partiel. Les25 liaisons et3089 archives sont intactes. Aucun contre-exemple analytique démontré. Tentative close ; nouvelle révision SOURCE des rayons arrondis vers l’extérieur en préparation, nouvelle autorisation interne nécessaire avant calcul. Les compilations H1 restent non exécutées ; officiel62modules/1049déclarations auxiliaires, aucune victoire.

ψ auteur01 : Core seul exécuté10:28:31–10:29:02 UTC, exit1/aucun olean. Composition non réduite et notation intégrale mal lexée ;3 modules suivants non invoqués.17prints standards/2sorryAx générés ne constituent pas un PASS. Log et reçu conservés. Révision02 distincte de54déclarations autorisée sous STOPFIRSTFAIL après56bindings/6476cache/3089archives vérifiés. Aucun contre-exemple analytique/parité établi ; officiel62/1049inchangé, H1/D_N/WIN ouverts.

Γ–Mellin auteur01 : ΓDerivative PASS auteur8déclarations10:40:22–10:40:59UTC, en attenteJuge. ΓBox FAIL10:40:59–10:41:21UTC (APIvoisinage),3suivants noninvoqués.6517inputs/3089archives intacts. GateROOT initiale erronée corrigée avant toute invocation, versioninitiale conservée ; incident de contrôle, pasFAILLean. Officiel62modules/1049déclarations inchangé ; H1/D_N/WIN ouverts.

R01 thermique auxiliaire : exécution unique10:41:16–10:44:48UTC, exit0,46cas/19mutations/15certificatsisqrt,33bindings/35captures intacts ; résultatc436226…. Ne constitue pasle testcompletN=10^8. ψ02 : Core seul10:45:24–10:45:55UTC exit1, parseurintégrale unexpected ..,18printsstandards/1sorryAxgénéré/aucunolean,3suivants noninvoqués. Révision03 distincte SOURCE. Officiel62/1049inchangé,H1/D_N/WINouverts.

ψ03 : Core auteur PASS19 à10:59:30UTC, contrôle indépendant restant. Beta exit1 à11:00:03UTC : quatre erreurs API/simplification, aucun olean ; Integral et Dup non invoqués. Parseur des axiomes à corriger pour les sorties multilignes, sans affaiblir le rejet de sorryAx. ψ04 distinct réutilisera Core en lecture seule. Conservation65entrées/6476artefacts/3089archives. Aucun contre-exemple arithmétique établi, aucun crédit officiel supplémentaire ni H1/D_N/WIN.

Juge22 batch03 : ΓDerivative seul réellement compilé11:15:36–11:16:13UTC, exit0/8axiomes standards ; vraie borne Γ′ et Cauchy certifiés. Conservation6597entrées/90anciensJuge/3089archives/21captures. Officiel63modules/1057déclarations auxiliaires incluant définitions. Aucun crédit H1,C3/C5,coefficientN,D_N ou WIN.

ψ04 : Beta23 et Integral10 (vraie P1) auteur PASS, Dup2 FAIL technique ;3enfants uniques11:21:53–11:22:58UTC. Analytique02 : ΓBox12 auteur PASS puis ΓContour FAIL (composition ContinuousAt et API intégrale absente), Mellin et Inversion non invoqués ;2enfants11:26:43–11:27:29UTC. Reçus complets et hashes liés, conservation74/6476 et6524/24captures/3089archives. Jugeψ52 en préparation ; globalH1 numérique et formal, coefficientN,D_N restent ouverts. Officiel63/1057inchangé.

ψ05 : vraie duplication Γ/ψ auteur PASS2, enfantunique11:33:35–11:33:49UTC exit0, deux axiomesstandards, unwarninglinter. Quatre modulesψ désormaisPASSauteur54déclarations ;52enattentedecontrôleindépendantautorisé, Dup2 encoreàauditer séparément. Conservation84/6476. Aucun créditglobalH1/C5/D_N/WIN.

Juge22 batch04 clos : trois modules PsiCore19, BetaLimit23, Integral10 réellement recompilés indépendamment11:40:20–11:41:42UTC, tous exit0/52axiomes standards. P1 : vraie formule intégrale de Γ′/Γ pour Re(z)>0 avec intégrabilité, majorant construit, DCT et Jacobien réel. Conservation6648entrées/134anciensJuge/3089archives/26captures vérifiée ROOT. Officiel66modules/1109déclarations auxiliaires incluant définitions. H1,C3,C5 global,coefficientN,D_N et WIN ouverts. Aucun nouveau calcul globalN. ROLE4 écrit le nouveau producteur/checker ; ROLE3 assure le contrôle SOURCE numérique indépendant.

Contrat numérique thermique global SOURCE reçu :14bindings/9runtime/5nouveaux vérifiés ROOT, paramètres N=1e8/Y=1e4/T=100/X=Q=R=1e6,204800nœuds verticaux/12288Arch/999999certificats prévus. Transport catalogue corrigé, dual16, mutant primal4 seul. Aucun résultat numérique/gate/PREPARED ni coût mesuré. Checker structurel ne certifie pas les primitives ; revue indépendante ROLE3 et enveloppes papier ROLE5 en cours. Launcher SOURCE ROLE4 en rédaction. Officiel66/1109 inchangé, H1/C3/C5/additif/D_N/WIN ouverts.

Deux revues indépendantes SOURCE/PAPER closes : C5SOURCE74 cohérent à lecture, dépendances et Mellin/Arch encore ouverts ; enveloppes du contrat thermique cohérentes à spécialisationfixée sous restrictions exactes de domaine. W/C8 exigent Y>=1, Eprim décroissance, Q>=2,R>=2 ; continuité ne remplace pas validité des majorants. Tous les budgets exigent des outputs effectifs ; checker structurel ne certifie pas primitives. Nouveau Jugebatch05 Box12→Contour11 en préparation distincte, aucune gate/compilation. Officiel66/1109 inchangé, H1/C3/C5/additif/D_N/WIN ouverts.

Juge22 batch05 clos et observé : Box12→premier Contour corrigé11, vrais enfants12:37:05–12:37:50UTC tous exit0/23axiomes standards. Enveloppe continueL1Gamma=(27/5)Y^(3/2)exp(-piT/4)/(pi/4), domaines Y>=1,c[-1/2,3/2],T>=0,abs(epsilon)=1 ; continuité/domination/intégrabilité réellement dérivées.6707inputs/209anciensJuge/3089archives/32captures conservés. Officiel68modules/1132déclarations avec définitions. Revue indépendante producteur numérique close sur papier,14bindings/9runtime stables et domaines explicités ; pas de run/guard numérique effectif. Préparation du lancement uniqueROLE6, limites3600s/2GiB. H1/C3/C5/C6/global/coefficientN/D_N/WIN ouverts.

Préparation globale01 : échec METADATA constaté avant toute gate/calcul, manifest1binding/préparation2 au lieu de toutes14sources/9runtime et fermeture. Sort-Object path -Unique sur OrderedDictionary a réduit la liste ; les assertions de chiffres annoncés ne valent pas couverture des paths. Source14bytes stables, six fichiers01 conservés ; actual inexistant et aucun enfant numérique. Réparation02 distincte avec map parpath et égalité de set complet. Aucun FAIL identité/Goldbach/parité/Lean global ; officiel68/1132 inchangé et H1/D_N/WIN ouverts.

La préparation distincte02 corrige le défaut metadata01 : 1003 fichiers hashés, 14 sources, 9 alias, 972 runtime ; les six anciens01 restent conservés. ROOT gate numérique créée c19adc, lancement réel unique ROLE6 5f24b4/session97614 ; START enfant 2026-10-03 13:03:11UTC. Paramètres N=10^8,Y=10000,T=100,X=Q=R=10^6 fixés, limites3600s/2Gio, no retry ; aucune garde ni identité globale validée à ce stade. Revue primitives/restes au niveau papier et checker structurel restent distincts. ROOT gate batch06 C5 créée a13cb2 pour neuf sources88 déclarations, au plus9 enfants arrêt premierFAIL. Officiel68/1132 inchangé. SOURCE Mellin vers Arch se poursuit ; H1/C5global/coefficientN/D_N/WIN ouverts.

Juge22 batch06 clos : EulerDirect indépendant PASS5 (4 théorèmes,1def), puis Reflection54e32a FAIL technique aux lignes94/124/131 ; sept aval NONINVOQUÉS. Aucun crédit des prints de récupération, aucun diagnostic de réfutation/parité. Deux enfants13:06:18–13:06:57UTC, source0d790e/olean555b10 Euler, dix erreursReflection sansolean ; ancienFAIL préservé.7019inputs/270anciensJuge/3089archives/64captures intacts vérifiés ROOT. Officiel69modules/1137déclarations avecdefs. Reflection07 corrigéecc39bd SOURCE noncompilée, prochainlot8/83 prépare. Calculnumérique global unique poursuit son cataloguefixe et limites ; H1/C5global/coefficientN/D_N/WIN ouverts.

Batch07 clos et observe : Reflection vraie zeta7 et Duplicationpsi2 PASS independants, ΓReflection8e070c FAIL API trois normalisations et cinq aval NONINVOQUES, zero credit FAIL et aucun contre-exemple analytique/parite. Trois enfants13:30:02-13:31:06UTC,7124inputs/374anciensJuge/3089archives/70captures intacts. Officiel71modules/1146auxiliaires avec definitions; Judge22 14PASS2FAIL techniques. Nouvelle ΓReflection08 SOURCE en preparation, prochainlot6/74 sous gate distincte. Numericunique toujours actif avec limites3600s/2GiB et parameters fixes, performanceSOURCE distincte sans invocation; Mellin/Arch SOURCE continue. H1/C5global/coefficientN/D_N/WIN ouverts.

Banque thermique globale02 : clôture effective MAX_WALL_SECONDS après3600s, un enfant et aucun retry ; 86400/204800 nœuds verticaux émis. Calcul incomplet : aucune comparaison globale, Etotal effectif, vérification finale ou mutants observés. Toutes1003liaisons/1005captures/3089archives conservées. Échec de ressources, sans falsification de l’identité ni conclusion sur la parité. Une version SOURCE optimisée distincte doit subir une revue indépendante avant tout nouveau contrat/gate. Officiel71/1146 auxiliaires ; H1/coefficientN/D_N/WIN ouverts.

Batch08 clos observe: GammaReflection08 PASS5 standard-only, Chi09 CONFIG_ROOT_PATH avant elaboration0print/olean et quatreavalNONINVOQUES; deuxenfants14:09:10-14:09:30UTC,7235inputs/489anciensJudge/3089archives/73captures intacts. Officiel72modules/1151aux avecdefinitions; Judge22 15PASS3FAIL(2API,1configuration), aucuncontreexempleanalytique/parite. Futurlot09racinecommune5/69, GammaReflectionreadonlyonziemedeps. Globalnumeric02CLOSMAXWALL3600s, derniercheckpoint86400, partialfile86507lignesmetadataROLE6; aucunecomparaison/Etotal/mutants. OptimizedSOURCEdistinctnewindependentreview/newcontract10800s/no gainmesure. Projection42 etMellin70SOURCE noncompiles, H1/coefficientN/D_N/WIN ouverts.

Batch09 closed: Chi09 independent PASS10 standard-only; Scaled FAIL three elaboration/normalization goals,6 recovery sorryAx prints and zero module credit;3 following modules NON_INVOKED. Two children14:40:08-14:40:51UTC,no replay.7348 inputs/604 closed Judge/3089 archives/75 captures preserved. Official73modules1161declarations includes definitions, Judge22 16PASS4FAIL(3API,1root configuration), no analytic or parity counterexample. Projection62 SOURCE pending independent lot10; Scaled10 distinct SOURCE repair for future11. Performance03 SOURCE independently reviewed at PAPER level, actual1016 bindings PREPARED and new gate authorized10800s2GiB, no numeric result yet. H1/coefficientN/D_N/WIN open.

Banque globale03 réellement démarrée14:48:16UTC, un enfant ROLE6, plafond10800s/2GiB et zéro retry. Revue indépendante SOURCE/PAPIER des21sources et cinq outils close ;1016liaisons/1018captures et archives historiques vérifiées avant START, ancien calcul clos conservé. Aucun accord/Etotal/mutants encore acquis. Le banc reste en phase zéro ; la projection additive et son enveloppe62déclarations SOURCE attendent le lot10. La note Mellin uniforme est PAPER seulement et expose une dette de hauteur/quadrature àa=1/N. Officiel73modules/1161déclarations auxiliaires ; H1 formel, coefficientN, D_N et victoire ouverts.

Batch10 closed: one actual child Envelope42 FAIL unresolved implicit intervalIntegral measure at256:13,41standard prints and1recovery sorryAx, no olean, zero whole-module credit; Identity20 NON_INVOKED. START15:03:18 FIN15:03:57UTC;7858 inputs/722 closed Judge/3089 archives/22captures intact. Official73modules1161aux declarations includes definitions, Judge22 16PASS5FAIL(4API,1rootconfiguration); no analytic identity or parity counterexample. ROLE4 prepares distinct Envelope revision02 with explicit volume and unchanged statements; next batch11 reserved repaired42+untouchedIdentity20. Global numeric03 actual child running since14:48:16UTC,10800s/2GiB/no retry, no final agreement/Etotal/mutants. Continuous circle specification ROLE6 PAPER in progress, phase Gamma51 SOURCE only, H1/coefficientN/PP/front/D_N/WIN open. ROOT metadata observer first encountered renamed modules_passed field before any write; new metadata-only adapter fixes schema without modifying old helpers/receipts or replaying Lean/numerics.

Batch11 réellement clos : Envelope révision02 indépendante PASS42 (29 théorèmes et13 définitions), puis Identity20 FAIL technique cinq diagnostics sur quatre sites API, conjugaison, permutation de sommes et réduction bêta ; dix recovery sorryAx et dix impressions standards ne créditent aucun module Identity. Deux enfants15:32:39–15:33:33UTC, FIN global15:33:43 ;7903 inputs/765 anciens Juge/3089 archives/24 captures conservés. Officiel74 modules/1203 déclarations auxiliaires incluant définitions, Juge22 17PASS6FAIL (5API,1configuration). Aucun contre-exemple analytique/parité ; enveloppe continue2exp(aN)AB acquise, identité exacte encore ouverte. Futur lot12 réservé à Identity révision distincte20 avec Envelope PASS11 readonly, sans recompilation42. Banc numérique03 unique continue phase0, aucun Etotal/verdict/mutants final ; cercle N=1e8 PAPER audité indépendamment, producteur et ressources ouverts. Re2 G2/DOM/queues49 SOURCE non compilées, orthogonalité discrète SOURCE en préparation, H1/C5 global/coefficientN/PP/front/D_N/WIN ouverts.

Cercle coefficient N : contrat révision02 et revue indépendante PAPER conservés ; aucune évaluation du coefficient à N=1e8, aucun producteur préparé. Les coûts et gardes restent explicites. Re2 :49 déclarations SOURCE non compilées, revue indépendante en cours. Prochain lot Lean réservé à Identity révision02 avec Envelope PASS11 readonly. Banc03 phase zéro continue son unique enfant ; aucun résultat final observé. Officiel74/1203 inchangé ; H1/D_N/WIN ouverts.

Batch12 réellement clos : un seul enfant Identity20 révision02 FAIL API à43:2, coercition du produit2*pi dans hperiod non normalisée ; les quatre diagnostics11 corrigés ne réapparaissent pas. Treize impressions standards et sept recovery sorryAx ne créditent aucun module, aucun olean. START15:58:01 FINenfant15:58:25 FINglobal15:58:35UTC ;7951 inputs/815 anciens Juge/3089 archives/23 captures conservés. Officiel74 modules/1203 auxiliaires incluant définitions inchangé ; Juge22 17PASS7FAIL (6API,1configuration), aucun contre-exemple analytique/parité. Révision03 distincte8bb1eb SOURCE corrigecast, futur13 réservé à Identity20+EnvelopePASS11 readonly ; discret29 autonome SOURCE reporté14. Banc03 a effectivement FIN16:03:41 exit0 et statut numérique auxiliaire SOURCE_AUDITED selon ROLE6, lecture/contrôle ROOT de clôture encore requis ; aucune certification Lean H1 ni coefficientN effectif, D_N/WIN ouverts.

Banque thermique03 réellement close NUMERICAL_AUX_PASS_SOURCE_AUDITED, un enfant14:48:16–16:03:31UTC, FIN parent16:03:41, aucun retry/replay.204800 nœuds verticaux,12288 Arch,999999 entiers effectivement traités ; 1016 bindings/1018 captures/3089 archives et ancien banc02 conservés. Gardes et comparaison déclarées validées par le producteur audité SOURCE/PAPIER et checker structurel, qui ne recalcule pas les primitives. Aucun nouveau crédit Lean ni H1 formel, trace de zéros complète, coefficient additifN, D_N ou WIN. Projection/NTT/PP/frontière restent ouverts.

Actual batch13 AUX_PASS one module20 declarations18theorems2definitions, all20 prints standard only, no sorryAx, readonly Envelope11 not recompiled. Continuous actual vonMangoldt projection and limit are paid as auxiliaries; H1 spectral uniform evaluator, numerical coefficient N1e8, PP removal, D_N and WIN remain open. All protected inputs preserved, no retries or old-bank replays.

Boucle22 : Identity13 effectivement AUX_PASS20 et Envelope11 AUX_PASS42 ; officiel75modules/1223aux. Banque03 phase zéro close, accord numérique SOURCE/PAPER avec contrôle structurel, E_total<1e-8<tau et3mutants disjoints selon les reçus du ROLE6 ; elle ne teste pas le coefficient de Goldbach. Discret29 révision02 et inversion Gamma-Mellin11 demeurent SOURCE sans compilation. Contrat CIRCLE NTT final lié par19bindings, N=M=1e8/K=2^27/S=2^58/a=0 fini, enveloppe et gardes définies ; producteur/checker natifs, précision formelle et contrôles effectifs encore ouverts. Six rôles sont répartis dans le temps ; H1 global/D_N/WIN restent ouverts.

Actual FAIL14 unique Discret29 revision02: four technical diagnostics dependent Decidable under ite at92/114, real-complex normalizer cast196 and Int negation cast285. All29prints22standard7recovery sorryAx, noolean/no partialcredit, conservation8015inputs911closed3089archives20captures. Continuous Identity20 and Envelope42 remain paid. No mathematical counterexample or parity blockage observed; new revision03 SOURCE only. CoefficientN1e8, native/log certificates, H1/D_N/WIN remain open.

Lot15 réel clos AUX_PASS29, unique d35455/session93472->e7fa47 exit0 ; 1module20theoremes9definitions,29prints standard seuls0sorryAx0empty,7linterwarnings0errors. Sources03 f24c702 intacts8060inputs956anciensJuge3089archives24captures. ROOT06ac27/c7608d FULL puis observation physique v2 prior75/1223 vers76/1252,19lotsPASS8FAIL historiques conservés. Identité CIRCLE finie vraieLambda/allPP raccord continu acquise ; NTT/catalogue/logs complets/coefficientN1e8 et H1/D_N/WIN ouverts. Aucun replay/retry numérique ou Lean et aucun16préparé.

PARAMETER_GUARD01 : gate ROOT distincte après revue indépendante SOURCE,1005bindings/19anciensNTT/3089archives conservés. Unique futur enfant ROLE6,60s/1MiB/0retry, seuls paramètres et5échantillons de log ; aucune NTT globale/coefficientN/build natif/Lean autorisés. Aucun résultat numérique anticipé, H1/D_N/WIN ouverts.

PARAMETER_GUARD01 revision02 actual AUX_PASS : unique parent cf3e25/session93619, enfant exit0 et5parametres/5logs/4mutants conformes au scopeSOURCE audite ; ROOT conserve physiquement1005inputs3089archives et original/copie de chaque capture. Primitives PAPER seulement ;0creditLean, pascatalogue complet/NTT/coefficientN1e8/H1/D_N/WIN. Ancienguard01 jamais lance et source/gate preserves.

Lot16 réel clos TECHNICAL_FAIL0modules0decl,1child873df7/session84428->b25998 exit1,Envelope14NON_INVOKED.4raccordsAPI logSeriesinverse/Ratcast151190/absRat236,38prints29std dontclampInteger empty1+9recovery sorryAx,pasolean,0creditmodule. ROOT21999f/87a8b5 FULL et conservationphysiquev2 8112inputs1006anciensJuge3089archives23captures ; officiel76/1252 inchangé,19PASS9FAIL dont8API1config. ROLE3 corrige52dansrévision03distincte sansauthorcompile/probe ; aucuncontreexempleanalytique/parité déduit, sources/acquispreservés,H1/D_N/WINouverts.

Boucle22 lot17 reel clos 17728e/session24652->0500a6 exit0 : deux modules auxiliaires PASS52=32theoremes20definitions,0erreur/0sorryAx,clampInteger seul sans axiome. Construction canonique log32 et precision1/S, vraie Lambda avec PP, enveloppe coefficient E continue et garde2E<=1e-6 maintenant compilees. Officiel78modules1304declarations incluant definitions. Conservation8160inputs1054anciensJuge3089archives24captures; ROOT observation physique sans Lean ni numerique. C++ natif/catalogue/NTT/CRT et coefficient completN1e8,H1,D_N,WIN ouverts; score0 de suivi sans propagation et node15.3 running. Premier observateur7c4f36 bloque avant toute ecriture par un digest recopie incorrectement; metadata corrigee, aucune compilation relancee. Aucun replay.

Contrat continu revision03 livre, SHA af466104a72bb89b5e0a5e7ecf117c06c610d23d14a82139cfda7cb96c6fcb82, ROOT FULL7695a7/c5accc. Identite13, discret15 et quantification/enveloppe17 compiles, officiel78/1304 auxiliaires. Catalogue natif/coefficient complet N1e8 et D_N/WIN ouverts; aucune nouvelle evaluation ni credit de ce rapport.

Boucle22 contrat continu final avec identites13/15 et precision/enveloppe17 compilees; officiel78/1304 auxiliaires. SOURCE natif02/BUILD02 et correctionCWD revus; preflightROLE6 conditionnel, loaderglobal non paye et aucunbuild/programme/banc coefficientN1e8 effectue. AnciensSOURCEs/3089archives intacts, ROOT metadata uniquement. D_N/parite/WIN ouverts; node15.3 running, score0 sans propagation.
Livraison: round22/role3/continuous_contract_delivery22_revision04.txt SHA f6cdd64d1f1d7853ed91ebdd004a46b97fbf49bd1b7964b52e140974f3af8e32; ROOTFULL helper806e34;native-handoffs85df77/847a97;reviews01-02-460d6e;build02-handoffplan791d81;reviewbuild02d00541;conditionalpreflight-supportd921b5/readse3db90;delivery04-5eca27/reads85845a

Reprise utilisateur continue: officiel78modules1304declarations auxiliaires, identites thermiques11/13/15 et precision/enveloppe17 compilees. SOURCE GammaMellin11 prepare pour Judge18 sans recompile anciens; BUILD03 revise le perimetre de confiance statique Windows/GCC sans faux loaderglobal et sans execution des .exe. SOURCE projection corpsfini en parallele, compiler gate et bankN1e8 distincts; D_N/WIN ouverts.

Lot18 reel clos:1 module invoque exit1,11prints=5standard6sorryAxrecuperation,0credit;composition/membership/reduction API techniques,aucune refutation analytique/parite. Officiel78modules1304declarations auxiliaires conservees. SOURCEFiniteField24 et reparationGamma distinctes;BUILD03 scopeWindowsGCC explicite en preparationmetadata,aucun build/bancN1e8 encore. PP/frontiere,D_N/WINouverts.

BUILD03 unique parent exit1, Win32 SetInformationJobObject1314 before compiler creation; zero compiler/produced execution. Conserved6358inputs/30captures/3089archives. SOURCE04 resource repair and Gamma11 repair distinct, Judge19 FiniteField24 preparing; official78/1304, global D_N/WIN open.

Lot19 reel PASS:FiniteFieldProjection22 exit0,24declarations20thm4defs et24printsstdonly(2propext,22triplet),2lints0error,sanssorryAx. Officiel79modules1328declarations auxiliaires. ProjectionexacteA32sousdomainesprime/root explicites,5certificatsconcretsSOURCEenconstruction. Gamma11revision02SOURCEprepare;BUILD03Win32fail1314avantcompiler clos,BUILD04SOURCEressources enrevision. AucuncoefficientN1e8calcule,nifronts/PP/D_N/WINpayes.

ROUND22 lot20 auxiliaire clos : inversion réelle Gamma x>0, unique Lean exit0, 11 déclarations sans sorry ni axiome ajouté. Total officiel80 modules/1339 déclarations incluant définitions. FAIL18 technique conservé ; échange Lambda, argument complexe, coefficientN natif, D_N et WIN ouverts. Aucun ancien compile ou bank rejoué.

BUILD04 unique parent exit0, two compiler drivers exit0 and frozen images, no produced binary execution. Preserved6375inputs/47captures/3089archives. Official80/1339 unchanged; concrete Roots21 and numeric consumer source pending, coefficientN/D_N/WIN open.

ROUND22 lot21 clos FAIL technique OfNat/val :1 enfantRoots exit1,16 buts nonfermés,18prints dont10recovery sorryAx,0olean/0crédit ;Bridge noninvoqué. Officiel80/1339 inchangé. Archives3089 et8380inputs/35captures conservés. RévisionSOURCE02 distincte en cours, ancienFAILimmuable ; BUILD04 deuximagesconstruites sanscalculN, D_N/WIN ouverts.

ROUND22 batch22 independently PASS two modules and 28 auxiliary declarations (22 theorems, 6 definitions), 28 exact standard-only axiom prints, zero diagnostics and zero sorry/native/custom. ROOT observes official82/1367 from80/1339, rehash8441inputs/1330old/3089archives/95captures. Five concrete Lucas primes, primitive2^27 roots and canonicalA32 finite projections paid AUX only. OldFAIL21 preserved; native coefficientN1e8, machine CRT refinement, uniform spectral cancellation and D_N/WIN remain OPEN.

Lot23 actual 6e6eb3/session35018→a99b89exit1 clos : trois erreurs techniques de normalisation, 30 prints dont 11 recovery sorryAx, zero module/declaration credite, aucun olean. Conservation 7748 inputs/1459 anciens/3089 archives/81 captures payee. Baseline82/1367. Correction SOURCE distincte requise ; aucun D_N/WIN.

Lot24 actual190b68/session83206→43f2f6exit1 clos sans retry : erreur unique inverse-power redondante ligne123, 30prints26std4recovery, aucuneolean/aucuncredit. Conservation7855inputs/1562old/3089archives/81captures. Baseline82/1367. Correction SOURCE04 distincte demandee. D_N et WIN ouverts.

Numeric04 actual WATCHDOG3600s, parent exit1, producerexit0, checkerFIN/receipt/POST/coefficient absent; external conservation6456/66/3089/5/83 verified; no mathematical verdict, zero Lean credit, D_N/WIN OPEN.

Lot25 actual281111/session28861→852eb2exit0 clos : AngularMellinBorder22 exact30=22theoremes8definitions, tous axiomes standards,0sorryAx/0erreur, olean94e699cc. Conservation7965inputs/1666old/3089archives/81captures. Ajout1module30declarations donne83/1397 auxiliaires. Recurrence analytique et bord q1 nonnul payes ; phase/signe global/D_N/WIN ouverts. Numeric04WATCHDOG3600s sans verdict clos separément.

Lot26 actual23b2e1/session53965→0bc7a2exit1 conserve : Local entierPASS22=16theoremes6defs, aucunrecovery ; HolFAIL7diagnosticsTECH/6recovery0credit. Conservation9020inputs/1770old/3089archives/91captures+2deps. Ajout1/22 donne84/1419 auxiliaires ; vraieGamma domination et L1 fixes payees, inversion complexe finale et signeζ/D_N/WIN ouverts. Source03Hol repair requiert nouveau juge27, aucun replayLocal.

Lot27 clos PASS15 indépendant, inversion Gamma complexe Re(w)>0 payée; conservation9138/1890/3089/94; officiel85modules1434déclarations incldefs, ζ/Weil/C5global/coef1e8/PP/D_N/WIN ouverts. Source05 délai révisé en cours, zéro nouvelle exécution numérique.

Numeric05 one checker PID23088 running, no verdict; Gamma inversion27 PASS15 closed, official85/1434; Tail22 SOURCE review pending; D_N/WIN open.

Lot 28 clos : FAIL technique de trois raccords API, neuf diagnostics et sept récupérations sorryAx ; zéro module ajouté. Baseline 85 modules et 1434 déclarations auxiliaires. Conservation physique des 9260 entrées, 2010 anciens fichiers, 3089 archives et 96 captures. Révision Tail distincte en préparation SOURCE ; native05 checker unique actif sans verdict. Aucune obstruction analytique déduite des erreurs API, aucun signe Goldbach ni D_N ni WIN validé.

Lot29 clos FAILED : le dernier site ContinuousAt.comp conserve deux diagnostics et un sorryAx de récupération ; module entier zéro crédit et aucun olean. Baseline 85 modules / 1434 déclarations auxiliaires. Les9389 inputs,2134 anciens fichiers,3089 archives et100 captures sont intacts. Source Tail03 en réparation distincte, Lambda main30 gelé en revue SOURCE ; numeric05 unique toujours sans verdict. Aucun obstacle analytique ou de parité déduit des erreurs API ; D_N et WIN restent ouverts.

CLOSED_STOP_NO_MATHEMATICAL_VERDICT; external6576/109/3/5/3089 conserved, no native Lean refinement or D_N/WIN.

Lot30 clos PASS : queues Gamma et rayon reel R continu effectivement compiles sans sorry, 22 declarations auxiliaires dont 4 definitions. Officiel86modules1456declarations. Echange vrai Lambda selectionne pour outils SOURCE31 seulement; bridge2 et E_Lambda16 restent non compiles. Native05 clos STOP sans coefficient; annulation canonique, geometrie compacte, D_N et WIN ouverts.

Batch31 actual FAILED on interval notation, Finset.range2 normalization and n=0 simplification; no olean, no whole module credit, no mathematical or parity refutation; distinct SOURCE repair delegated ROLE4; bridge2 selected separately for SOURCE tools32 only.

Batch32 independently PASS whole exponential-tail bridge2: exp(-w)-G_H=TGamma and norm bounded by continuous R for Re(w)>0 and H>=0; exact two standard axiom rows, no errors/recovery; adds one auxiliary module/two theorems only, no weighted Lambda tail, numerical coefficient, parity sign or D_N/WIN. Source33 dynamic baseline preparation remains future gated.

R22 actual33 FAILED technique un enfant sans timeout ni reprise: normalization Continuous(lambdaMellinCoefficient 0)149:4;30prints25standards5sorryAx,aucunolean,zero whole-modulecredit. Physical9945inputs2673old3089archives108captures intacts. Official87modules1458auxdefs inclus unchanged; tools34 futurePASS33 prerequisite blocked,distinct SOURCE03 repair and future35 required. No signed cancellation,D_N,coefficientN1e8 or WIN.

ROOT closed scalar radius point01: independent unique Python child exit0, exact rational upper bound below tau at the fixed N=1e8/H=1e11 point as reported by ROLE4; 39 frozen files preserved. This is Mellin-height radius only under PAPER connectors, no coefficient/identity/D_N/Lean credit/WIN. Official baseline remains87/1458.

Round22 actual35 closes the real Gamma-Lambda Mellin identity on Re(w)>0 and Q<=6 with all prime powers: one fresh whole-module PASS30 (24 theorems,6 definitions),0errors/0recovery,one unused-hypothesis warning; 10092 inputs/2819 prior files/3089 archives/103 captures preserved. This adds1/30 to87/1458 after ROOT verification, with no zeta/Weil, canonical sign, coefficient computation,D_N or WIN. Failures31/33 and stopped sixDRAFT34 remain immutable; next distinct source selection may target E-Lambda16 and Geometry25.

Clôture36 observée : échec technique réflexion118:6, zéro crédit, Geometry non invoquée. Baseline88modules/1488déclarations auxiliaires inchangée. Directive humaine : gel ingénierie pour SynthèseV3 et transfert théorie ; aucune nouvelle compilation, aucun coefficient N=10^8 ni borne D_N ni WIN.

## Gel humain et Synthèse V3 — 4 octobre 2026

Session d’ingénierie gelée à la demande du chercheur. Aucun nouveau Lean, natif ou calcul scientifique. Bilan : 88 modules / 1488 déclarations auxiliaires, définitions comprises ; Mellin principale PASS30. Le test rationnel du majorant scalaire à N=10^8 passe, mais le raccord complet du rayon de troncature au coefficient reste non compilé. Lot36 : échec technique de réflexion, crédit nul ; géométrie non invoquée ; correctif EΛ02 SOURCE seulement. Deux binaires construits ; dernier contrôle natif du coefficient terminé sans verdict. D_N et WIN restent ouverts. Livrables de clôture : synthesis_v3/goldbach_synthesis_v3.tex, PDF, preuves documentaires et consigne de reprise théorique.

Synthèse V3 finalisée : 17 pages, source autonome et archive arXiv ; compilation documentaire exit0, rendu contrôlé, 47 liens de preuve rehashés. Aucun nouveau test scientifique ; empreintes dans synthesis_v3/DELIVERY_V3.json. La publication GitHub conserve tous les fichiers du corpus gelé et les payloads trop volumineux sous forme reconstructible.

English Synthesis V3 finalized: 17 pages, standalone source and arXiv archive; compilation documentaire exit0, rendu contrôlé, 47 liens de preuve rehashés. Aucun nouveau test scientifique ; empreintes dans synthesis_v3/DELIVERY_V3.json. La publication GitHub conserve tous les fichiers du corpus gelé et les payloads trop volumineux sous forme reconstructible.
