# Agent 6 — vérification numérique de la boucle 11

**TERMINÉ.** Les deux contrats nouveaux ont été reçus, testés sur les arguments arithmétiques réels puis rejoués dans un dossier isolé. Les trois reçus sont identiques dans tous leurs champs JSON et dans tous leurs octets. Les identités finies passent ; plusieurs extensions fausses restent `ERROR_FALSIFIER`, rejetées avant compilation. Le rôle 6 n'a appelé aucun compilateur Lean. Il ne revendique aucun gain global sur D_N.

## Conservation et paramètres

Le registre `previous_artifacts_sha256.json` protège **405 fichiers**, dont **64 fichiers de la boucle 10**, en incluant Judge, sources, oleans produits, logs, PNG et controller final. SHA du registre : `f86a31f72d624124338afad6932cd859dceae164a6f3422f9b8998164fcf9e05`. Les vérifications avant et après chaque banque et chaque rejeu donnent `PRESERVED`. Le SHA de controller10 reste `c48e0480b9f227c9e404c1322dacb239d81720d9242ecb45e05037df8f177b2f`.

Les deux sources originales sont conservées : PDF `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24`, ZIP `32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd`. Le helper neuf exclut les répertoires `roundNN` de numéro supérieur ou égal à 11, les caches, `.arbor`, `.git` et REPORT.md central vivant. Les modifications ou additions dans les anciennes boucles restent détectées. Aucun ancien banc PASS n'a été exécuté.

N=100000000, alpha=100, a=3163 et Q=999999 original. Les valeurs des seuils sont exactes en entiers : 99^4<N<=100^4 et 3162^16<N^7<=3163^16. Les deux noyaux appariés utilisent le même front strict a*k<m, le cap Q et leurs unités réelles. W est le noyau source avec log(k/m), sans changement de signe vers W_positive. Les helpers historiques sont chargés par chemins explicites avec SHA, sans bytecode.

## Contrat 2 : coefficient lcm et préfixe entier

`ap_prefix.json` donne `PASS_NEW_FINITE_CONTRACTS_ONLY`. Le lemme B6 est vérifié sur P=3003=3*7*11*13 et les seize diviseurs r|P :

```
sum_(d|P) mu(d)/phi(lcm(r,d^2))
  = (1/r)*product_(p|P,p not dividing r)(1-1/[p(p-1)]).
```

Le support d|P est distinct du support d<=D de la tête AP. Sur le produit fini avec masques d unitaires, les ratios r=3,7,21 sont exactement 2/5,6/41,12/205. Le coefficient r=9 est zéro, tandis que le produit carré-libre appliqué illicitement donnerait 2/5. Le coefficient r=5 est zéro par le masque unitaire ; la suppression de ce masque donne V_P/4. L'intersection r=d=3 impose lcm(3,9)=9, phi=6 ; le produit incorrect 27 donne phi=18. La restriction incorrecte gcd(r,d)=1 retire aussi une cellule nécessaire. Ces trois extensions sont des falsifications hors des gardes de B6, pas des échecs de B6.

La tête AP et la queue carrée sont vérifiées sur **la même sélection E** de cinq vrais premiers unitaires : 68952733,99999073,99999517,99999589,99999989. Les douze couples de cut dans {100,3163} et D dans {1,2,3,16,3216,3217} conservent toutes les intersections. Chaque Ψ'_E utilise cette sélection identique. L'égalité tête+queue est vérifiée contre le détecteur carré-libre calculé indépendamment. Le Ψ' global n'est pas énuméré.

Le témoin neuf m=31047267=3*3217^2, n=68952733 premier, a mu(m)=0. À D=16, la tête vaut −log3*log68952733 et sa queue +log3*log68952733 ; retirer la queue donnerait un résultat faux. Le témoin m=927=3^2*103 a n=99999073 premier, m divisible par9 mais pas27 : la vraie cellule AP lcm9 existe, celle du produit27 est vide.

Le bas et la bande sont distincts. Pour m=11, n=99999989 premier, U_alpha=−log11 et la bande est nulle. Pour m=411=3*137, n=99999589 premier, U_alpha=−log3 et la bande +log3, donc U_a=0. Remplacer le préfixe entier par la bande fausse le raccord physique avec sa référence.

Le nouveau témoin m=483=3*7*23, n=99999517 premier, donne exactement [mu(m)^2 Lambda(m)+S(N)mu(m)]/S(N)=−1. Il réfute seulement le minorant pointwise non négatif. Le produit infini S(N) et son moment global ne sont pas évalués numériquement.

La puissance propre nouvelle n=9, m=99999991=7*13*769*1429, est unitaire. Le poids premier Ψ' vaut zéro ; Lambda_N(n)=log3 est non nul, tandis que mu(n)^2 Lambda_N(n)=0 et le multiplicateur raw Lambda(n)−log n vaut −log3. Cette distinction conserve les puissances propres du premier axe sans prétendre énumérer le raw entier.

## Contrat 1 : deux incidences premières et faces complètes

`paired_axes.json` donne `PASS_NEW_PAIR_IDENTITY_ONLY`. Chaque branche raccorde le vrai bracket theta_N(n)[−mu(m)(D_a−W_a)] à theta_N(n)[Lambda(c)+mu(c)W_a] dans J2. L'égalité ALL-k / k>=2 est contrôlée ; les deux noyaux W distincts sont entièrement calculés, sans remplacement par leur principal. Les signes sont certifiés par intervalles rationnels de logarithmes, avec assertions strictes excluant un résultat UNRESOLVED pour les réfutations.

| Paire neuve | Incidences | Principal normalisé | Paire réelle |
|---|---|---|---|
| c=1, p=3167, q=3169 | n=89963777 et n3=69891331 premiers | négatif | positif |
| c=1, p=3167, q=3191 | n=89894103 composite, n3=69682309 premier | positif | positif |
| c=7, p=3167, q=3169 | n=29746439 premier, face3c absente | positif | positif |

La première paire conserve l'entropie +log3*log69891331 et les deux W. Un principal de modèle négatif ne garantit donc pas une paire entière favorable. La seconde a theta_N(n)=0 ; son principal normalisé est +log69682309, alors que le faux quotient log(n3/n) est négatif. La troisième conserve son terme sans partenaire : 3m=210760683>N. Chaque réfutation vise le transfert précis testé, sans no-go global.

La partition entière est aussi vérifiée sur les **deux** t=p*q : C_t=9, X_t={1,3,7}=D_t{1} disjoint 3D_t{3} disjoint F_t{7}. La somme des vrais brackets égale la somme des paires et des faces. P2 est vérifiée comme identité en un scalaire S(N) non évalué. Pour t=10036223, Delta_common=log(69891331/89963777), Delta_single=0 et Delta_face=+log29746439. Pour t=10105897, Delta_common=0, Delta_single=+log69682309 et Delta_face=0 parce que le complément de 7t est composite. La face géométrique reste dans la partition même lorsque son indicatrice première est zéro.

À cette taille les bases conjointes d non divisibles par3 et avec mu(d)=−1 n'existent pas dans D_t={1}. Le coût positif analytique P5 n'est donc pas validé par ces tests. Les termes bénéfiques, célibataires, faces et entropies restent visibles.

## Rejeu et portée

`replay_checks.py` exécute exclusivement les trois producteurs neufs avec `--output-dir round11/isolated_output_probe`. `numerical_replay.json` donne `PASS_NEW_ROUND11_BYTES_AND_FIELDS_REPLAY`, trois codes de sortie zéro, tous les champs et octets égaux, entrées canoniques inchangées et conservation `PRESERVED`. Les SHA des helpers, producteurs, reçus et rapports mathématiques gelés y sont consignés.

Le gate B6 sauvegardé est transmis au rôle 3 et le gate P1/P2 complet au rôle 4 avant leurs compilations. Une falsification mathématique n'est pas appelée erreur du compilateur. Les drapeaux global_D_N, asymptotic, payments, Lean_called et victory sont tous false. Les preuves écrites des paiements, de Mertens, du crible conjoint et de BV relèvent de leurs audits formels ; aucune de ces bornes n'est testée à log(10^8). Le seuil source reste u>=10^24, avec un seuil BV supplémentaire non évalué.

Le ledger D_N=B_prime^a+B_pp^a+P_band+Z_face+I_alpha+2max(e,0) reste entier. Les quatre Möbius HH et la phase native1 sur q|k ne sont pas modifiés par les tests présents ; aucune réduction du raw par un masque mu(n)^2 n'est faite. Le contrôle porte sur ces nouveaux contrats finis et conserve les postes ouverts nécessaires à la cible.

SHA des gates : AP `84d4cd68709aa9a16fd4a96d44374726c427b3cce40df9b364b1eae8c474d917` ; paire `ff1f8526553f2861776e9aa3f492969274a664055b8e3fb6ea41bebe079c6173` ; rejeu `ed729a029fbe35338220c0e1d9dad3b9d11692b63e2446ddbafce558e8f570a1`.
