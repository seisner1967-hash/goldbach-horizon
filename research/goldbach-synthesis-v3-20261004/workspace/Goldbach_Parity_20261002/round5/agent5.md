# Agent 5 — Juge indépendant, boucle 5

## Verdict et reproduction

**Statut : PARTIAL. Victoire : NON.** Le replay indépendant sous Lean 4.15.0 compile **26 nouveaux théorèmes** : 15 dans `DeterminantCoordinates.lean`, 11 dans `UnitSupportedCompletion.lean`. Les deux codes de sortie sont 0 ; les 26 audits `#print axioms` n'exposent que des sous-ensembles de `propext`, `Classical.choice`, `Quot.sound`. Aucun token de code `sorry`, `admit`, `axiom` ou `native_decide` n'est présent.

Commande complète de reproduction :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round5\build-judge.ps1'
```

Le builder impose les filtres numériques et la conservation des 120 artefacts gelés, reconstruit `CompositeCompletion.lean` **depuis le texte conservé de la boucle 4**, puis recompile les deux nouveaux modules dans `round5\judge\output`. Aucun ancien `.olean` de recherche n'est repris. Les 12 déclarations de cette dépendance sont réauditées, soit **38 audits de déclarations pour ce replay**, dont 26 nouvelles. Les résultats distincts de l'ensemble des boucles totalisent maintenant **116 nouveaux théorèmes compilés**.

Les hashes des sources, résultats compilés, journaux, filtres et compilateur sont dans `round5\judge_receipt.json`. Les journaux indépendants sont dans `round5\judge\logs`. La version du compilateur est 4.15.0, commit `11651562caae`, avec les huit packages mathlib du cache compatible, hors réseau. Le SHA256 du source gelé `DeterminantCoordinates.lean` est `aafce8f549d2824b1bcf2910e2f331acdb01beebe59a7350bc68525ae46f0413`, conforme à la notification de l'Agent 3.

## Conservation et rejeu numérique

Le registre `previous_artifacts_sha256.json` protège **120 sources, scripts, reçus, journaux et builders précédents**. Son SHA256 est `b2a48fef1f5eccbc30ed516a0f5e20bd20042cb559aa997ac2d38602ddc32558`. Le rapport central vivant, l'état du contrôleur et les caches sont exclus explicitement du registre. Les 120 hashes ont été vérifiés avant le calcul numérique indépendant puis, à nouveau, après le replay Lean. Le statut reste **PRESERVED** ; aucun ancien artefact n'a été modifié.

Le vérificateur local `round5\verify-frozen.ps1` contrôle directement chaque hash du registre. Le builder le fait avant et après les compilations ; les résultats de conservation sont également consignés dans le reçu final.

Le wrapper `round5\judge\numerical\replay.py` importe les scripts originaux inchangés et redirige seulement leur export vers son dossier isolé. Les deux JSON rejoués sont exactement égaux aux originaux, sans champ exclu et avec les mêmes SHA256 :

| Filtre | Statut | SHA256 original = replay |
|---|---|---|
| hecke.json | PASS | e67b46ab0405408b1b295815fb88172579ec15fe22acaf5437e613552fbe8bed |
| frequency.json | PASS | e3048b49b8d175db4528046b17cb2e6769cd6368b1323e0587d54f70c5922d36 |

Les phases et leurs produits sont des vecteurs de coefficients entiers réduits par division cyclotomique exacte. Les quotients HNF et les masques sont vérifiés en arithmétique entière. Aucun nombre flottant ne décide une identité ou un signe.

## Portée de DeterminantCoordinates

Le fichier démontre les deux quotients entiers A=(u+lambda*D)/N et C=(s−lambda*B)/N sous les hypothèses explicites de divisibilité, leur reconstruction, la factorisation matricielle `M=H_lambda*G`, et `det G=1` lorsque N>0 et `u*B+s*D=N`. Les formules inverses préservent ces identités. Les quotients des facteurs originaux B=b*v*x et D=k*t*z sont eux aussi reconstruits sous leurs conditions de divisibilité et de non-nullité appropriées.

`exists_canonical_lambda_of_coprime` démontre l'**existence** d'un lambda dans `0≤lambda<N`, avec les deux divisibilités, depuis `gcd(N,B)=1` et le niveau de déterminant. L'hypothèse de coprimalité est explicite ; le fichier ne prétend pas la supprimer. Il ne fournit pas un théorème distinct d'unicité, ni une bijection déjà réindexée entre tous les ensembles finis du HH original. Les fenêtres, caps, positivités et poids ne sont pas invariants par la seule factorisation matricielle.

Le témoin concret a N=10^8, lambda=73626461 et les deux bases entières de déterminant un certifiées. Le shear −78 garde la même matrice H_lambda et le niveau N, mais transforme v=7 en v=75469=163*463, et s=7951 en s=7717 premier. **Lean démontre que le produit réel des quatre Möbius du tuple développé passe de +1 à −1.**

Cette déclaration concerne `mu(u)*mu(v)*mu(s)*mu(t)` pour un tuple développé. Elle n'est pas le coefficient déjà agrégé `H_y(a)*H_y(r)` ni une assertion sur le moment HH entier. Le banc numérique calcule séparément ce coefficient agrégé et trouve 4 puis 0 ; cette seconde constatation demeure celle du filtre fini, pas une conclusion tacite ajoutée au théorème Lean.

Sur les 204 shears positifs déclarés, 43 gardent les masques originaux : 24 signes développés positifs, 19 négatifs. Les autres shears conservent le déterminant, mais peuvent perdre l'unité ou la carré-liberté. Le module CRT original a*r est conservé dans les données et varie. La constance automatique du poids signé sur la classe HNF est donc falsifiée ; aucune éventuelle compensation **pondérée** sur la classe complète n'est réfutée par ce seul témoin.

## Portée de UnitSupportedCompletion

Les conventions complexes sont conservées : tau(chi) et tau(chi inverse) sont deux sommes distinctes. Les théorèmes établissent la conjugaison de Gauss et

`kappa = chi^(-1)(−1)*tau(chi^(-1))*tau(chi) = normSq(tau(chi))`,

où le membre réel est plongé dans les complexes. L'identité de moment unitaire C7 impose **explicitement** `F(z)=0` pour chaque z nonunitaire :

`H_F = chi^(-1)(−1)*tau(chi)*M_F`.

En utilisant la complétion composite avec toutes les fréquences, le fichier démontre

`tau(chi^(-1))*H_F = kappa*M_F`,

`E_nonunit(F) = (q−kappa)*M_F`,

et la double identité C10 avec le facteur exact `(kappa/q)^2`. La normalisation et les deux Gauss ne sont pas remplacés par des expressions de valeur absolue.

**M_F reste un moment complexe signé.** Le fait que kappa soit une norme carrée réelle ne lui donne pas un signe favorable et ne contrôle pas sa taille. Aucun énoncé de primitivité ou de conducteur n'est supposé. Les formules générales de descente ou d'induction C1–C6 ne sont pas prétendues formalisées par ce fichier, et aucune borne de kappa en fonction du conducteur n'y est démontrée.

Les deux caractères d'ordre quatre modulo 5 et 10 du filtre vérifient précisément ces conventions : tau(chi) diffère de tau(chi inverse), kappa vaut 5, et le moment physique a des composantes complexes. Le calcul modulo 10 avec F=delta2 réfute C7 sans l'hypothèse de support unitaire. Une dépendance de F et G aux autres variables de la cellule reste dans leurs moments ; ces identités n'affirment pas la séparabilité des masques HH couplés.

## Diagnostic des fréquences

Le filtre explore les 81 strates divisorielles de N=10^8 et **89988 égalités de phases rationnelles échantillonnées**. La partition de cardinalité N découle structurellement de la somme exacte des phi(q'), sans énumération complète de cent millions de fréquences.

Pour le caractère induit modulo 5, l'argument d'orbites conserve 8 fréquences actives dans les strates q'=5 et 10 ; chacune contribue 50000000 à la masse ponctuelle. Le défaut nonunitaire total est N lorsque la somme de Gauss unitaire s'annule. Les petits modules 15,100,385 sont des diagnostics distincts, exhaustifs seulement sur ces modules déclarés.

Le benchmark N=70630, h=2 et q'=35315 conserve une contribution non nulle d'un caractère de conducteur 5. Il falsifie la règle générale « petit conducteur implique petit module réduit actif ». Ce constat est un diagnostic numérique arithmétique ; aucune identité générale de descente en conducteur n'a été acceptée comme théorème Lean dans cette boucle.

## Erreurs techniques et falsifications mathématiques

| Tentative | Diagnostic | Statut de preuve |
|---|---|---|
| Determinant compile01 | La matrice développée contenait `0−D` au lieu de `−D`; une tactique séquentielle provoquait aussi un avertissement. | Échec technique, preuve dépendante non reçue. |
| Determinant compile02 | Quatorze théorèmes compilés ; une suggestion de tactique restait affichée. | Identités réparées, version intermédiaire. |
| Determinant compile03 | Quatorze théorèmes sans diagnostic. | Version intermédiaire acceptée. |
| Determinant compile04 | Ajout du certificat des deux bases canoniques, quinze théorèmes. | Version finale confirmée par le Juge. |
| Unit support compile01 | La réécriture de la permutation x→−x rencontrait un produit dont l'ordre différait ; deux hypothèses de section étaient inutiles. | Échec technique de représentation. |
| Unit support compile02 | Une simplification générique de négation atteignait la limite de récursion dans la synthèse d'instance. | Preuves aval de conjugaison non reçues. |
| Unit support compile03 | La simplification générique récursait encore. | Échec technique, sans conclusion analytique. |
| Unit support compile04 | La réécriture explicite `chi inverse(−x)=chi inverse(−1)*chi inverse(x)` remplace la simplification générique ; onze théorèmes sans diagnostic. | Version finale confirmée par le Juge. |

Ces erreurs Lean ne sont pas le mur de la parité. Les falsifications mathématiques concernent la descente non pondérée des signes à une classe HNF, la suppression du support unitaire, la confusion des deux Gauss et l'inférence automatique d'un petit module actif. Aucun journal d'échec n'est reçu comme preuve.

## Obligation restante

Les coordonnées et les identités de complétion sont exactes, mais aucun cumul signé avec les poids réels, fenêtres, modules CRT et frontières mobiles n'est estimé. Le changement de signe d'un tuple ne produit pas une compensation du moment agrégé. La positivité de kappa ne produit pas une positivité du moment physique complexe. Avec le raccord acquis `D_N=−Sfull+2*max(e,0)`, **la cible `D_N≤N/(256 log N log log N)` demeure non démontrée**.
