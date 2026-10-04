# Agent 3 — formalisation des projecteurs de parité

## Environnement retrouvé

Le ZIP fourni ne contenait aucun fichier Lean. Les définitions déjà formalisées sont disponibles dans `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Research_20260930\goldbach_sprint15_checked.zip`, et leurs sources/replays dans `sprint15\lean` et `sprint15\agents\full_project_replayfresh`. Les sources `GoldbachArithmetic.lean`, `GoldbachMoebiusComplement.lean`, `GoldbachMoebiusShortLong.lean`, `GoldbachRoughCofactors.lean` conservent respectivement la séquence réelle, le changement de diviseur complémentaire, les quatre secteurs short/long et la fusion des coefficients sur la fibre rugueuse. Aucun fichier acquis n'a été modifié.

Compilateur local : `C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe`, version 4.15.0, commit `11651562caae`. Les huit bibliothèques précompilées existent sous `D:\Users\Utilisateur\Desktop\Maths\q356-canonical-binding-replay\.lake\packages\{aesop,batteries,importGraph,LeanSearchClient,mathlib,plausible,proofwidgets,Qq}\.lake\build\lib`. Le fichier lake de l'ancien sprint3 fixe mathlib au commit `9837ca9d65d9de6fad1ef4381750ca688774e608` ; ce renseignement décrit la configuration archivale, pas une reconstruction réseau récente.

Aucun `AGENTS.md` n'a été trouvé aux racines Maths/projet/sprint15 inspectées. La compilation préparatoire utilise le répertoire préexistant `full_project_replayfresh` pour les seules dépendances Goldbach importées ; le Juge pourra reconstruire ces dépendances dans son nouveau répertoire pour une vérification fraîche indépendante.

## Résultat exact produit

Nouveau fichier : `lean\ParityWeights.lean`. Les définitions s'appuient sur le `muReal` réel déjà utilisé dans `GoldbachArithmetic` :

`Podd(m) = (muReal(m)^2 - muReal(m))/2`,
`Peven(m) = (muReal(m)^2 + muReal(m))/2`.

Sur facteurs coprimes, les deux identités bilinéaires exactes sont :

`Podd(ab) = Podd(a) Peven(b) + Peven(a) Podd(b)`,
`Peven(ab) = Peven(a) Peven(b) + Podd(a) Podd(b)`.

Les réponses prime/semiprime/triprime valent respectivement `(1,0)`, `(0,1)`, `(1,0)`, sous primalité et distinction explicites des facteurs. La positivité, l'idempotence de Podd et l'orthogonalité des deux projecteurs sont également prouvées. Un triprime est prouvé non premier ; sa fonction de von Mangoldt est exactement nulle alors que Podd vaut un.

Le théorème concret `concrete_prime_triprime_same_parity` certifie que 101 et `101*103*107` donnent Podd=1, que ce dernier produit n'est pas premier, qu'il appartient à la fenêtre `100<m<10^8`, et que tous ses facteurs premiers sont strictement supérieurs à 100. Cette contre-réponse conserve donc réellement une frontière rugueuse, et ne dépend pas d'un test empirique.

## Journaux des tentatives

`logs\agent3_parity_compile01.log` : erreur naturelle de `nlinarith` dans la démonstration de non-primalité, le produit de trois facteurs demandant une borne intermédiaire. Les commandes `#print axioms` suivantes ont exposé `sorryAx` pour les déclarations dépendant du but échoué. Ce fichier est un journal d'échec, aucun artefact correspondant n'est reçu comme preuve.

`logs\agent3_parity_compile02.log` : la réparation introduisait `p<p*q≤p*q*r`, mais `omega` n'avait pas reçu explicitement `1≤r`, et la conclusion intermédiaire conservait `p*q*1`. Erreurs de tactique et de simplification, sans rapport avec une impossibilité analytique. Réparation : fournir `hr.one_lt.le` et simplifier `Nat.mul_one` dans l'hypothèse.

`logs\agent3_parity_compile03.log` : compilation de la version réparée, code de sortie 0. Les 19 théorèmes impriment uniquement les axiomes standards `propext`, `Classical.choice`, `Quot.sound`, sans `sorryAx`, avertissement ni erreur. Le fichier source n'utilise aucune déclaration d'axiome et aucune preuve omise. Les deux journaux précédents restent conservés. L'olean résultant est `lean\ParityWeights.olean`.

## Portée et raccordement

Une égalité bilinéaire de projecteurs n'établit aucune économie sur le résidu terminal D_N. L'obstacle précis se voit déjà sur `m=101*103*107` : l'information de parité seule confond un premier et un produit de trois premiers distincts. La correction hypergraphe proposée par l'Agent 1 doit soustraire la masse des triprimes sur le domaine où Ω≤3. Dans le domaine rugueux général de la monographie, les parités positives 3, 5 et 7 subsistent et doivent être traitées avec leurs sélecteurs d'origine.

Le lemme manquant est une estimation signée avec gain suffisamment fort de ces corrections et/ou du secteur long-long complet, uniformément sur les supports et faces mobiles de D_N. Ni la fusion de μ, ni les identités XOR, ni la borne positive de cofacteur court fournie dans le ZIP n'apportent ce gain. Aucun résultat ci-dessus n'est déclaré victoire au sens demandé.
