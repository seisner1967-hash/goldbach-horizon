# Agent 5 — Juge indépendant Lean 4

## Verdict final des trois fichiers

Le replay indépendant du Juge réussit : `ParityWeights.lean` (**19 théorèmes**), `QuarticMobius.lean` (**11 théorèmes**) et `ChenWeight.lean` (**8 théorèmes**) compilent sous Lean **4.15.0**, codes de sortie **0**. Les **38 nouveaux théorèmes** ont été contrôlés par `#print axioms` : seuls `propext`, `Classical.choice`, `Quot.sound` apparaissent. Aucun des quatre tokens interdits (`sorry`, `admit`, `axiom`, `native_decide`) n'est présent dans le code des six sources rejouées. L'audit lexical exclut les commentaires Lean imbriqués, les commentaires de ligne et les chaînes ; il ne traite pas une mention explicative d'axiome dans un commentaire comme une déclaration. Cette constatation porte sur le code Lean, pas sur les rapports qui décrivent les tentatives échouées.

**Résultats partiels certifiés, aucune victoire déclarée.** Les deux identités bilinéaires des projecteurs sont démontrées pour le vrai coefficient de Möbius ; l'inversion quartique avec reste exact et son insertion pondérée réelle le sont aussi. Un détecteur polynomial de premiers est prouvé sur le secteur complètement rugueux à multiplicité bornée. Le compilateur certifie également la limite des projecteurs : un produit de trois premiers distincts conserve le projecteur impair égal à un, bien qu'il soit composé et que son von Mangoldt soit nul. Ces diagnostics respectent le cadre fixé et ne remettent aucun acquis historique en question.

## Reproduction et provenance

Commande hors réseau depuis PowerShell :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\build-judge.ps1' -NewModules @('ParityWeights', 'QuarticMobius', 'ChenWeight') -ExtraDependencies @('GoldbachMoebiusShortLong')
```

Le script copie les sources de `GoldbachBridge`, `GoldbachArithmetic` et `GoldbachMoebiusShortLong` depuis l'archive de travail du sprint 15, puis les reconstruit dans **le nouveau dossier** `judge\dependencies`. Il reconstruit les trois nouveaux fichiers dans `judge\output`. Aucun `.olean` Goldbach acquis ni `.olean` d'un nouveau fichier n'est repris comme preuve. Seul le cache des huit packages mathlib compatibles est réutilisé. Les sources historiques demeurent inchangées.

Compilateur : `C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe`, version 4.15.0, commit `11651562caae`.

Le reçu `judge_receipt.json` conserve la version et le SHA256 du compilateur, le `LEAN_PATH` exact, les hashes des deux filtres numériques acceptés, les hashes des sources, journaux et résultats compilés, les codes de sortie, et les dépendances axiomatiques de chaque déclaration imprimée. Les journaux bruts se trouvent dans `judge\logs`. Le replay des dépendances imprime respectivement 10, 15 et 15 déclarations ; celui des nouveaux fichiers imprime 19, 11 et 8 déclarations, soit **78 audits axiomatiques au total**, dont 38 nouveaux théorèmes.

Le filtre `numerical\numerical.json` est **PASS à N=100000000** avant cette compilation indépendante. Il est une vérification finie exactement délimitée, sans portée asymptotique.

## Où les tentatives ont échoué

`logs\agent3_parity_compile01.log` : `nlinarith` ne reconstruit pas automatiquement la chaîne multiplicative nécessaire pour montrer `p < p*q*r`. Certaines déclarations aval impriment alors `sorryAx` à cause du but échoué. Ce journal ne vaut pas preuve et son artefact n'est pas retenu.

`logs\agent3_parity_compile02.log` : `omega` manque de l'hypothèse explicite `1≤r`; la borne intermédiaire contient encore `p*q*1` au lieu de `p*q`. Ce sont des échecs d'automatisation et de simplification. Ils ne constituent pas un échec imposé par le mur de la parité. La réparation consiste à fournir `hr.one_lt.le` et simplifier `Nat.mul_one`.

`logs\agent3_parity_compile03.log` et `judge\logs\ParityWeights.log` : la réparation compile, sans preuve incomplète. Le second journal est un replay frais indépendant.

Une erreur préalable du script du Juge provenait de `ConvertFrom-Json`, qui traite autrement les clés `N` et `n` : `-AsHashtable` l'a corrigée. Ce problème n'était pas une erreur du compilateur Lean.

## Blocage mathématique précis

La déclaration `concrete_prime_triprime_same_parity` prouve dans Lean que `101` et `101*103*107 = 1113121` ont tous deux `oddWeight = 1`, alors que le second est composé, se situe entre `100` et `10^8` et possède seulement des facteurs premiers supérieurs à `100`. Elle établit une contre-réponse arithmétique dans le secteur rugueux complet de ce test.

L'identité `oddWeight(ab) = oddWeight(a)*evenWeight(b) + evenWeight(a)*oddWeight(b)` organise donc correctement la parité multiplicative ; elle conserve aussi la contribution positive des triprimes. La preuve n'assume aucune estimation souhaitée, mais elle ne fournit pas un contrôle permettant d'éliminer cette contribution dans la convolution additive réelle.

Sur le domaine carré-libre quart-rugueux avec au plus trois facteurs, la correction triprime ou le poids d'interpolation de l'Agent 1 peut détecter exactement les premiers. La détection ponctuelle n'est pas, à elle seule, un contrôle des incidences signées avec `Lambda(N-m)` sur les supports et frontières mobiles. Le lemme manquant est un contrôle arithmétique effectif de ces incidences, ou une autre implication démontrée qui permet à l'identité de contourner l'aveuglement du crible dans le résidu exact. Il n'est pas demandé ici de formaliser toute la conjecture de Goldbach pour reconnaître un tel mécanisme, mais la simple réécriture de la même masse ne suffit pas.

## Replay de l'identité quartique de l'Agent 4

Le filtre numérique C est PASS avant compilation : 18866 vérifications exactes, dont 8192 cas des deux faces à `N=100000000`, `alpha=100`. Ce domaine fini est déclaré par l'Agent 6 ; il ne comprend pas tous les entiers inférieurs à N.

`QuarticMobius.lean` formalise l'identité entière dans l'anneau des fonctions arithmétiques, avec coefficients 4, −6, 4, −1 et reste `longMoebius(alpha)^4 * zeta^3`. Le support exact du reste est nul pour `n<(alpha+1)^4`. La variante appliquée utilise `n<N≤alpha^4`. Le théorème `weighted_boundary_identity_real` accepte un ensemble fini d'indices arbitraires et un coefficient réel arbitraire `c(t)` : il remplace seulement le facteur `mu(r(t))` lorsque `alpha<r(t)<N`. Il n'injecte aucune estimation ni hypothèse de compensation dans c. L'indice complet peut conserver les modules CRT ar, les caps, les logarithmes et les masques ; aucun module CRT n'est raccourci par la preuve.

`logs\agent4_quartic_compile01.log` : un `ring` s'exécutait après clôture du but ; une constante `ArithmeticFunction.sub_apply` n'existe pas dans la version du cache ; `Nat.pow_le_pow_left` nécessitait l'exposant 4 explicite. Ces échecs de représentation et d'interface propageaient une preuve incomplète dans les conclusions aval.

`logs\agent4_quartic_compile02.log` : dernière différence de normalisation entre les numéraux 4 et 6 dans l'anneau des fonctions arithmétiques et les coefficients entiers après application ponctuelle. Des lemmes locaux explicitant leur application réparent cette représentation. Aucun de ces deux journaux ne vaut preuve, ni preuve d'un obstacle analytique.

`logs\agent4_quartic_compile03.log` puis `judge\logs\QuarticMobius.log` : compilation réparée puis replay frais indépendant, tous deux code 0 ; les 11 déclarations n'ont que les axiomes standards. Les identités dans l'anneau et le support quartique n'étaient pas les parties logiquement défaillantes des premiers essais.

L'inversion quartique est une identité standard de type Heath–Brown, dont la famille figure déjà dans le corpus. Son insertion sur la frontière complète retire une occurrence de Möbius sur un long argument, mais maintient le cumul signé des incidences −6,+4,−1 et leur couplage au premier de l'autre axe. Elle ne prouve ni leur signe favorable ni le gain nécessaire à la cible. La capacité d'estimer cette nouvelle représentation reste à établir.

## Replay du poids Chen à multiplicité réelle

Le filtre B supplémentaire `numerical\chen_multiplicity.json` est **PASS avant compilation** : 24121 cas à `N=100000000`, `alpha=100`, incluant 1204 carrés premiers, 65 cubes premiers et 21648 produits `p²q` distincts. Le script du Juge impose ce filtre lorsque `ChenWeight` figure parmi les modules à reconstruire ; son hash, le nombre de cas et le hash du script numérique sont conservés dans le champ `supplemental_numerical_gates` du reçu final. Le reçu numérique original n'est pas réécrit par le Juge.

Le source final `ChenWeight.lean` a pour SHA256 `65a38665aeae858ce465b26b64ade993a64aae8127a50deac022ccc7103b48ff`, identique à celui communiqué pour la relecture indépendante. `factorCount` désigne le vrai `ArithmeticFunction.cardFactors`, donc Ω avec multiplicité. Le poids `W=(Ω−2)(Ω−3)/2` prend les valeurs 1,0,0 sur Ω=1,2,3. Le fichier démontre la borne Ω≤3 en utilisant les occurrences de la liste des facteurs premiers et la borne de produit `(alpha+1)^Ω≤n`. Les hypothèses `1<n`, `n<(alpha+1)^4` et la rugosité complète de n sont explicites ; aucun carré-libre n'est supposé, aucune borne souhaitée du résidu n'est utilisée.

`weighted_prime_identity_real` conserve un coefficient réel arbitraire sur les indices complets. Il détecte uniquement la primalité de l'argument auquel W est appliqué. La frontière `r>alpha` ne fournit pas la rugosité complète de r ; même un cofacteur r complètement rugueux ne rend pas automatiquement `m=k*r` complètement rugueux. Et r premier ne rend pas m premier lorsque k>1. Le détecteur appliqué au complément m exige donc les hypothèses pour m lui-même, sur le support original. Les nombres 0 et 1 sont correctement exclus du détecteur par `1<n`.

Le terme Ω(Ω−1)/2 compte des paires d'occurrences, avec valeurs premières éventuellement égales : il ne peut pas être réinterprété comme une somme restreinte à p<q sans l'hypothèse carré-libre correspondante. L'information sur Ω dépasse la seule parité, mais son acquisition arithmétique et surtout son moment signé avec `Lambda(N-m)` ne sont pas estimés par le lemme. La détection exacte locale ne devient pas automatiquement une estimation efficace des poids sur les supports et grands modules initiaux.

`logs\agent4_chen_compile01.log` : une réécriture du produit des facteurs premiers remplaçait simultanément n dans la longueur de la liste et dans le membre droit ; elle empêchait l'unification avec le lemme de produit. Un `calc` conservant la longueur originale répare cet échec technique. Les déclarations aval imprimaient l'axiome de preuve incomplète ; ce journal n'est pas reçu comme preuve.

`logs\agent4_chen_compile02.log` puis `judge\logs\ChenWeight.log` : compilation réparée puis replay indépendant, tous deux code 0. Les huit théorèmes n'ont que les axiomes standards, et `lower_bound_list_product` dépend seulement de `propext`. La relecture mathématique distincte `agent3_review_chen.md` confirme les restrictions de domaine et l'absence d'estimation du moment réel.

**La borne `D_N ≤ N/(256 log N log log N)` n'est démontrée par aucun des trois fichiers.** La compilation de 38 théorèmes est acquise ; le verdict de victoire reste faux car aucun mécanisme démontré ne contourne encore l'aveuglement du crible dans le résidu exact.
