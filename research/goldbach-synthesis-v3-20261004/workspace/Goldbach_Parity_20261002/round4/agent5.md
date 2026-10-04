# Agent 5 — Juge indépendant, boucle 4

## Verdict

**Statut : PARTIAL. Victoire : NON.** Les deux sources finales ont été rejouées indépendamment sous Lean 4.15.0 : **9 théorèmes** dans `AffineHHObstruction.lean`, **12 théorèmes** dans `CompositeCompletion.lean`, codes de sortie 0. Les 21 nouveaux `#print axioms` ne contiennent que `propext`, `Classical.choice`, `Quot.sound`. Aucun token de code `sorry`, `admit`, `axiom` ou `native_decide` n'apparaît. Aucun nouvel énoncé n'assume la cible de D_N pour la renommer.

Les résultats certifient une obstruction affine précisément délimitée et une inversion de complétion avec défaut nonunitaire explicite. Ils ne démontrent aucune borne du moment HH ni du résidu terminal.

## Reproduction, dépendances et conservation

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round4\build-judge.ps1'
```

Le builder, le reçu et les journaux sont distincts de ceux des boucles précédentes. Le compilateur est Lean 4.15.0, commit `11651562caae`, exécuté directement hors réseau. Les huit packages mathlib compatibles du cache local sont réutilisés. Les deux fichiers finaux importent **uniquement mathlib** : aucune dépendance Goldbach personnalisée, y compris QuotientGauss, n'est requise ou importée depuis un ancien `.olean`.

Les deux sources sont recompilées dans `round4\judge\output` ; le chemin de chargement exclut les répertoires des anciens `.olean` personnalisés. Les hashes avant et après compilation coïncident. Le SHA256 de `AffineHHObstruction.lean` est `9e3274b7f220bd59b49a31abff47301451f907eb6af8ebcb38a653f07d1e9baa`, conforme à la notification de gel. Le reçu `round4\judge_receipt.json` conserve les autres hashes, les codes de sortie, les axiomes et les chemins exacts.

Les builders et reçus antérieurs demeurent inchangés. Leur conservation, ainsi que celle des sources et reçus numériques précédents, est vérifiée dans le reçu de rejeu numérique séparé. Les 21 nouveaux théorèmes portent à **90** le nombre total de nouveaux théorèmes distincts compilés dans les quatre boucles, sans conférer une portée analytique aux identités finies.

## Rejeu numérique isolé avant compilation

Les scripts `affine_checks.py` et `inverse_checks.py` ont été relus puis réexécutés via `round4\judge\numerical\replay.py`. Le wrapper importe leurs sources originales et ne redirige que le dossier de sortie. Les deux nouveaux JSON sont **exactement identiques**, champ par champ et par SHA256, aux reçus originaux. Aucun champ n'a été exclu de la comparaison.

Les sorties isolées et le reçu avant/après sont sous `round4\judge\numerical`. Tous les anciens fichiers numériques et les builders/reçus des boucles précédentes inspectés ont conservé leurs SHA256. Les deux filtres originaux et le rejeu indépendant PASS sont des préconditions du builder Lean.

Le filtre affine vérifie 12400 couples indépendants de formes dans le domaine exhaustif de coefficients indiqué, ainsi qu'un chart de rang un avec 303 points positifs testés et 25 faces HH unités et carrées-libres. Il conserve les contre-exemples de dégénérescence et de N nul. Ces tests finis ne démontrent pas une uniformité asymptotique.

Le filtre d'inversion conserve toutes les phases en coefficients entiers et les réduit modulo les polynômes cyclotomiques exacts. Pour les masses ponctuelles :

| q | conducteur | tau² | défaut nonunitaire E | projection double unitaire normalisée |
|---:|---:|---:|---:|---:|
| 11 | 11 | −11 | 0 | 1 |
| 15 | 3 | −3 | 12 | 1/25 |
| 100 | 5 | 0 | 100 | 0 |

La masse physique correspondante vaut un. Oublier le défaut nonunitaire est donc faux pour les deux cas composites. À N=10^8, l'argument d'orbites de longueur cinq pour le caractère induit modulo cinq donne tau=0 : il couvre structurellement le groupe des unités, sans énumération des quarante millions d'unités. Ce diagnostic numérique n'est pas une nouvelle déclaration Lean démontrant la nullité de cette somme particulière.

Le benchmark couplé conserve C=s*t dans la longueur de F_C : pour C=33, la masse physique exacte vaut 1 ; figer la fenêtre à C=21 donne 2. Cette falsification interdit de supprimer cette dépendance pour obtenir artificiellement des poids séparés.

## Portée exacte du certificat affine

`common_zero_of_nonzero_determinant` construit explicitement le zéro commun de deux formes affines à déterminant non nul sur un corps. Le théorème central suppose :

`∀ X Y : K, A(X,Y)*R(X,Y)+B(X,Y)*S(X,Y)=N`, avec `N≠0`.

Cette universalité permet d'évaluer l'identité au zéro commun et prouve que le **déterminant croisé** des gradients de A et B est nul. R et S sont des fonctions partout définies ; aucun transfert d'une boîte finie ou d'un point entier vers une identité universelle n'est inclus dans la preuve.

Les variantes rationnelle et réelle sont des spécialisations de ce résultat. Elles ne constituent pas une formalisation du lemme complet de rang total un en dimension supérieure. Le fichier démontre expressément qu'un facteur nul permet deux directions indépendantes dans une même branche sans contribution à la somme. La non-dégénérescence reste donc indispensable à un éventuel lemme plus fort.

`exact_mixed_product_difference` conserve le terme b*h*j du niveau HH. Le tuple positif concret à N=10^8 appartient au niveau initial ; ses déplacements mixtes produisent exactement 1040. Ce certificat falsifie la linéarisation qui omet le terme croisé, mais n'exclut ni des charts non linéaires ni toute approche d'uniformité supérieure.

## Portée exacte de l'inversion composite

La source impose seulement `q≠0` par `NeZero q`, sans primalité ni primitivité du caractère. `fourierWeight` utilise la phase négative et est reliée au DFT standard. L'inversion additionne **tous les h** dans ZMod q. La partition entre unités et nonunités est ensuite démontrée, avec `nonunitDefect` défini par la somme réelle des termes nonunitaires.

Pour tau=gaussSum(chi inverse), le théorème certifie exactement :

`tau*H = q*F_moment − E_nonunit`.

La variante normalisée divise uniquement par q, dont la non-nullité complexe est prouvée. La variante double donne :

`tau²*H_F*H_G/q² = (F_moment−E_F/q)*(G_moment−E_G/q)`.

**Aucune division par tau n'est utilisée.** Le corollaire sous l'hypothèse explicite tau=0 conserve `q*F_moment=E_nonunit`; il ne déclare pas ce défaut négligeable. La fréquence h=0 est certifiée nonunitaire sous `Nontrivial (ZMod q)`, hypothèse nécessaire pour exclure le cas q=1.

Ces égalités restent ponctuelles pour les poids F et G donnés. Si ces poids dépendent de C ou d'autres données de la cellule, leur dépendance demeure dans les moments et les défauts. Le produit de deux moments ne factorise pas automatiquement un sélecteur HH couplé. Le fichier ne transfère pas une estimation de caractère primitif à tous les conducteurs d'un module composite et ne prouve aucune petitesse du défaut.

## Erreurs techniques et falsifications mathématiques

`logs\agent3_compile01.log` : Lean ne pouvait inférer les constantes c et f dans le lemme du zéro commun, car l'hypothèse sur le déterminant ne les mentionne pas. Les arguments explicites `(c:=c)` et `(f:=f)` réparent cette erreur d'élaboration. Les conclusions dépendantes du but échoué n'étaient pas recevables. `agent3_compile02.log` et le replay du Juge compilent les neuf théorèmes réparés.

`logs\agent4_composite_compile01.log` : une réécriture nécessitait l'explicitation de la fonction sommée sur les unités ; `field_simp` réécrivait également le caractère inverse en `1/chi`, créant deux expressions de somme de Gauss différentes pour la normalisation. La preuve réparée normalise le produit déjà démontré, puis divise par q.

`agent4_composite_compile02.log` : dernier but de commutativité, `q*F_moment=F_moment*q`, laissé après la simplification de corps. `ring` le clôt. `agent4_composite_compile03.log` et le replay indépendant compilent les douze conclusions sans diagnostic.

Ces erreurs Lean sont techniques. Les falsifications mathématiques sont différentes : rang total sans hypothèse de non-dégénérescence, maintien du niveau HH après omission du terme mixte, suppression du défaut nonunitaire et gel d'une fenêtre dépendant de C. Aucun journal de compilation échouée n'est accepté comme preuve.

## Obligation restante

L'obstruction affine ne produit aucune annulation des quatre signes de Möbius sur le niveau multiplicatif. L'inversion composite réexprime exactement les moments physiques et leurs défauts ; elle ne les contrôle pas quantitativement. Le raccord acquis `D_N=−Sfull+2*max(e,0)` conserve donc son obligation de contrôle signé sur le support complet. **La cible `D_N≤N/(256 log N log log N)` n'est pas démontrée.**
