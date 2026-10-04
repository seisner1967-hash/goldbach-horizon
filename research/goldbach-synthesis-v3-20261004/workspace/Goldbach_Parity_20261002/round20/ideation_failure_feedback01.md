# Retour d’idéation20 sur les FAIL Lean4 01 et02

Observation statique au 2026-10-03 03:09:35 UTC. Les sources PREEXEC, les journaux et les START01/02 ont été lus intégralement, ainsi que FINAL2. Les définitions importées ont été lues aux endroits cités ; pour FINAL1, seules les lignes d’hypothèse ont été consultées ici. Aucune compilation, aucun calcul mathématique, aucune modification des sources auteur ou des FINALs. Ce rapport ne juge aucune tentative ultérieure.

**Conclusion : défaut tactique de traitement d’un quotient naturel par `omega`, sans contre-exemple arithmétique ni hypothèse de taille manquante décelée dans ces deux wrappers. Aucun obstacle de parité n’est atteint par ces erreurs.**

Les métadonnées réelles du registre auteur donnent : tentative01, START03:04:52.193095Z, FIN03:05:07.375906Z, exit1 ; tentative02, START03:06:20.062530Z, FIN03:06:34.968542Z, exit1. Aucune des deux entrées ne contient un olean déclaré réussi. Ces deux FAIL demeurent des échecs de compilation complets, même si plusieurs déclarations indépendantes présentent uniquement les axiomes usuels dans leurs impressions.

## Cause précise et gardes

[StructuralSupport19](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round19/judge/build/NonSSBracketSwitch.lean:17) contient réellement `M ≤ q`, `anchor N < e` et le cap `e*q + (N-1)/alpha + 1 ≤ N`. [ResourceCell19](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round19/judge/build/BalancedResourceSwitch.lean:20) et `anchor_three` fournissent la garde `3 ≤ anchor N`. Les ressources sont les différences naturelles [N−q et N−anchor(N)*q](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round19/judge/build/BalancedResourceSwitch.lean:13).

Dans [PREEXEC01](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt01_source_PREEXEC.lean.txt:13), les deux lemmes précédant les wrappers obtiennent `q+Q+1 ≤ resource0` et `3*q+Q+1 ≤ resource1`, avec `Q : ℕ := (N-1)/alpha`. Les impressions de leurs axiomes dans [log01](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt01.log:1) ne contiennent pas `sorryAx`. Le FAIL porte uniquement sur la déduction finale de `M ≤ resource0/1` aux lignes40/46 de la source01.

Le modèle abstrait imprimé par `omega` laisse l’atome `c := ↑(N−1)/↑alpha` sans contrainte de non-négativité. [PREEXEC02](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt02_source_PREEXEC.lean.txt:36) isole les chaînages par `calc`, mais emploie encore `omega` pour `q ≤ q+Q+1` et `q ≤ 3*q+Q+1`. [Log02](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt02.log:1) rend la cause explicite : le premier modèle autorise `c ≤ −2`, le second `2*b+c ≤ −2` malgré `b ≥ 0`. Ces possibilités concernent l’abstraction tactique ; elles ne peuvent représenter le quotient naturel original. Les énoncés restent bien typés. Ajouter une hypothèse analytique ou un nouvel onset ne répondrait pas à cette erreur ; la chaîne d’ordre naturelle doit être exprimée par des lemmes d’ordre, sans dépendre de cette abstraction. Aucune garde `alpha > 0` n’est nécessaire pour le seul fait `0 ≤ Q` dans `ℕ`.

Les `sorryAx` des wrappers et des couvertures aval sont des dépendances produites par les objectifs échoués. Les sources01/02 ne contiennent aucun `sorry` explicite. Leur absence textuelle ne rend pas les FAIL recevables : les couvertures utilisent les wrappers et ne sont pas validées par ces tentatives.

## Préfixe et conséquences pour les deux pistes

Le certificat [primeFactorsList_prefix_divisor](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt01_source_PREEXEC.lean.txt:78) porte sur une **liste avec multiplicité**, décomposée en `first ++ rest`, dont `first.prod` divise la ressource et vérifie `D ≤ first.prod < D*Y`. Les gardes `1<D`, `0<Y`, `D≤n` et `Smooth Y n` sont explicites ; la non-nullité de n et les facteurs ≤Y viennent de `Smooth`. Aucun carré libre de d, aucune coprimalité entre d et n/d ni aucun facteur distinct n’est ajouté. [Les couvertures physiques](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt01_source_PREEXEC.lean.txt:107) conservent explicitement `D≤M` : le raccord source de cette garde reste distinct. Une bande inclusive jusqu’à DY est un majorant du préfixe strict, pas un remplacement de ses répétitions.

- **Piste2 friable :** conserver le mécanisme FINAL2 et réparer le chaînage de taille. Ces FAIL ne réfutent ni le préfixe ni la preuve papier. Ils ne prouvent pas non plus le paiement : les [sommes Euler, TK et le budget F4](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/agent2_friable.md:126) restent à formaliser et à raccorder aux paramètres source. Le coût des fronts, l’union physique des réciproques et [F0 privé de F1](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/agent2_friable.md:188) restent dans leur périmètre déclaré.
- **Piste1 soustraction composite :** les deux erreurs ne concernent pas ses identités Selberg/Bonferroni ou les conducteurs AP exposés dans [l’hypothèse FINAL1](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/agent1_switched_composite.md:24). Elles n’en modifient donc pas l’hypothèse d’idéation. Le reste AP, les grands facteurs, le raccord source et le gain total de Γ ne reçoivent aucun crédit de ce diagnostic.

Si les wrappers corrigés compilent ensuite, ce sera un raccord géométrique local. La victoire demandée exige toujours le contournement effectif de la parité et le raccord au résidu complet ; aucun PASS auxiliaire ne suffit.

## Entrées SHA256 observées

Les STARTs sont comparés à leurs sources PREEXEC ; les hashes des journaux correspondent aux entrées01/02 du registre auteur. Ce sont des hashes de fichiers, pas une nouvelle exécution mathématique.

| Entrée sous Goldbach_Parity_20261002 | SHA256 |
|---|---|
| round20/role4/attempt01.log | e32add28221a9cf95c0854239b1d03cce79124c21f44968d10ac6489e95d7941 |
| round20/role4/attempt01_source_PREEXEC.lean.txt | f13c30bd13f314bd1921054619a7ec7101c8496d228157da49348f4bfa7fa36f |
| round20/role4/attempt01_started.json | 3fe8dbe6c04ee4a90faa6811392885293a91e7a6d84570656a9a591250e9bd3f |
| round20/role4/attempt02.log | 632c0adc8e36937220a69424c2590e9da0475b168c8f5b20ed3dd09e36ef5d33 |
| round20/role4/attempt02_source_PREEXEC.lean.txt | 90902af848bda0d0d24c56f5385062823ec76c04baa8c6c7fa541bb61bde9cc8 |
| round20/role4/attempt02_started.json | 5d144a308bf0bcac5be3c9cf88252dfb07ae8ea97efc8937ec1c847199a379bc |
| round20/agent2_friable.md | 5635cff82cbd5e6e395dfef3617f8d2d89ead40f6dbbdfffa943bf0f6a785be5 |
| round20/agent1_switched_composite.md | 1c52ccfe6aaf393fe02b606ecbaeb56ae62810f0b93d6db604672ba560a241d9 |
| round19/judge/build/NonSSBracketSwitch.lean | 8d4cc04aa370c59deaa2672bad04df51f6bb937853344f3ec7e983d0033aa9db |
| round19/judge/build/BalancedResourceSwitch.lean | 310338aef835c39e461bfa92780bc394d68149d8ff1d1c9c622a886904ecb01f |

Traçabilité de lecture : FULL01 log/source/START `27a613`/`bf3033`/`fbd2e2`; FULL02 log/source/START `f094f7`/`45e273`/`14b05d`; FULL FINAL2 `db147b`; gardes `e2123a`; registre01/02 extrait `253362`; hashes `5b0e0f`. L’affichage initial du registre était tronqué et n’est pas revendiqué FULL. Une commande de hashes a eu une erreur de syntaxe PowerShell (`428bac`), corrigée par `5b0e0f` ; ce n’est pas un FAIL Lean ou numérique.
