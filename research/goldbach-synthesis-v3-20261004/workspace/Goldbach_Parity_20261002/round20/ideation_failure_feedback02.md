# Retour d’idéation20 : FAIL04/06, réparations05/07 et périmètre du paiement

Rapport statique, lectures terminées le 2026-10-03 vers03:23 UTC. Le rapport01 est conservé byte pour byte. FULL : sources PREEXEC04/05/06/07, journaux04/05/06/07 et leurs STARTs ; registre auteur décodé puis entrées04–07 extraites ; Payment8b5884ad et ses deux dépendances phase2 lus intégralement. Aucune compilation, aucun calcul mathématique ni modification des sources, FINALs ou gates. Aucune tentative08 ou ultérieure n’est évaluée ici.

**Les trois erreurs bloquantes réellement observées dans04/06 sont techniques. Les corrections05/07 gardent les mêmes énoncés et hypothèses. Leurs PASS auteur ne constituent ni F4 au source ni une victoire de parité.**

## Erreurs réellement observées et réparations

| Tentative | Horaires UTC START → FIN | Exit | Résultat pertinent |
|---|---|---:|---|
|04 EulerRankin|03:07:48.295604 →03:08:11.662019|1|`rw` ne voit pas le cast sous la projection `.toFun` du MonoidHom en construction.|
|05 EulerRankin|03:08:40.737916 →03:09:03.829261|0|`change` explicite la fonction réelle ; aucun `sorryAx` dans les impressions du log.|
|06 KernelEnvelope|03:09:21.663738 →03:09:41.913390|1|Implication résiduelle dans la preuve du produit non premier ; puis échec `omega` sur le cap avec Nat.div.|
|07 KernelEnvelope|03:10:54.787341 →03:11:14.732168|0|Branches du produit premier et ordre naturel explicites ; aucun `sorryAx` dans le log.|

**04, MonoidHom.** [Log04](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt04.log:1) indique que `Nat.cast_mul` ne trouve pas `↑(m*n)` dans un but écrit avec `{toFun := ...}.toFun`. [PREEXEC05](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt05_source_PREEXEC.lean.txt:15) ajoute uniquement `change ((m*n:ℕ):ℝ)^s = (m:ℝ)^s*(n:ℝ)^s` avant la même réécriture. C’est une explicitation définitionnelle ; aucune nouvelle sommabilité globale, aucune nouvelle hypothèse sur s. Le warning de séquençage et la suggestion `ring_nf` ne sont pas des erreurs mathématiques. Les `sorryAx` de04 se propagent de ce MonoidHom vers ses utilisateurs.

**06, produit non premier.** [Log06](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt06.log:1) laisse `Nat.Prime q → ¬e=1`, alors que `he : 1<e` figure dans le contexte. L’implication ne découle pas de la seule primalité de q : elle découle ici de la garde déjà présente sur e. [PREEXEC07](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt07_source_PREEXEC.lean.txt:47) ouvre `Nat.prime_mul_iff`, puis rejette q=1 par `hq.ne_one` et e=1 par `ne_of_gt he`. Le défaut est la fermeture par `simp`, pas l’énoncé ni une primalité manquante d’un quotient.

**06, cap et Nat.div.** La seconde erreur porte sur `e*q<N`. Le modèle abstrait de `omega` contient `i−j≥0` et `i−j+k≤−1`, où k représente le quotient naturel Q ; il omet la contrainte k≥0. Aucun tel modèle ne représente les naturels originaux. [PREEXEC07](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt07_source_PREEXEC.lean.txt:69) dérive `e*q+1≤N` par `Nat.le_add_right` et le cap, puis emploie `Nat.lt_of_succ_le`. Les gardes initiales sont conservées. Les identités cofacteur theta/raw deviennent alors recevables dans le PASS auteur07 ; elles conservent le vrai harmonicKernel et le premier axe raw von Mangoldt.

Les FAIL04/06 restent inscrits comme FAIL complets avec leurs sources PREEXEC et logs. Les PASS05/07 sont observés dans le registre et les logs stockés ; ce rapport ne remplace pas le Juge indépendant et ne les réexécute pas.

## Obligations mathématiques restant distinctes

La version [Payment8b5884ad](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/FriablePhysicalPayment.lean) est un texte de preuve examiné ici ; aucun PASS de ce module ou de ses dépendances phase2 n’est revendiqué dans ce rapport.

- **Euler/Rankin et TK.** PASS05 donne de vraies sommes sur les entiers friables, à support fini de premiers, et le vrai poids `tau=m.divisors.card`. Il n’assume aucune sommabilité globale à s=σ−1. PASS07 garde encore l’enveloppe supérieure conditionnelle sous [TotientSumBound](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt07_source_PREEXEC.lean.txt:127). `FriableTotientEnvelope` écrit une dérivation de TK à partir des vrais diviseurs, d’un Euler fini et du télescopage ; `FriablePrimeHarmonic` écrit Eplus≤u^27, la masse≤u^−37 et le tail tau≤N·u^−42. Ces dérivations doivent passer leurs propres compilations et être raccordées ; elles ne sont pas acquises par05/07.
- **F2.** [actual_friable_union_card_le_mass](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/FriablePhysicalPayment.lean:126) écrit, pour un e fixé et une vraie sous-famille S de StructuralSupport, `card S≤2[(N/e)·Σ_{d∈B_D}1/d+card B_D]`. Les deux classes et leurs +1 sont conservés ; `D≤M`, `1<D`, `0<Y` sont explicites. Cela est un ingrédient cardinal de F2. Le fichier8b5884ad ne contient ni l’agrégation des modules des demandes theta/raw sur tous les e, ni la borne7u³ pour chaque demande, ni la somme des fronts E·D·Y et son coût final `7N/u³³+28N^(97/128)/u³⁴`. Les identités raw07 ne doivent pas être remplacées par theta ou payées deux fois.
- **F3.** Les images `friableQ1` puis `uniqueResources1` fusionnent réellement les e avant consommation ; l’injectivité q↦N−q utilise q<N sur le support. [actual_unique_F1_reciprocal_payment](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/FriablePhysicalPayment.lean:344) écrit `U_F1≤7N·(log N)^−39` pour le vrai `sourceBracket` sous des gardes indépendantes : a≥1, M>0, logN≥1, logY≥4, 1+logY≤logN, logM≥3logN/4 et `128 loglogN logY≤logN`. Ce sont des gardes géométriques explicites, pas une petite somme libre. Elles doivent être dérivées des floors/ceils source ; un test fini ne les remplace pas.
- **Source et F4.** Le fichier ne définit pas le wrapper α/a/M/D/Y source, ne dérive pas ces gardes depuis u≥10^24 et ne contient pas la conclusion F4 `T_F+U_F1≤N/(8192u ell)`. Le raccord du sous-domaine H19 à tout le support source, les e=1/p0/singletons, Γ, T_A et le ledger complet restent distincts. La déclaration locale de F3 ne devient pas automatiquement cette conclusion source.
- **F0 privé de F1.** [FINAL2](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/agent2_friable.md:188) conserve le réciproque m1 non friable de ces fibres. Payment8b5884ad ne contient aucun ensemble ou coût qui le paie. L’Euler univarié de m1 ne contrôle pas sa corrélation avec la friabilité de m0. Le complément non friable et la capacité totale restent impayés.

Retour aux deux pistes d’idéation : garder leurs mécanismes. Ces diagnostics n’invalident ni le retrait friable ni la soustraction composite Selberg/Bonferroni ; ils ne fournissent aucun gain nouveau de Γ, aucune disponibilité et aucun contournement de parité. La prochaine conclusion admissible dépend des théorèmes effectivement compilés et de leur périmètre exact.

## SHA256 et provenance

Chemins sous `Goldbach_Parity_20261002`. Sources courantes EulerRankin/KernelEnvelope = snapshots PASS05/07 par hash. Les hashes des logs et STARTs correspondent au registre04–07. Les versions phase2 sont des observations statiques, pas des PREEXEC inventés ni des artefacts gelés par ce rapport.

| Entrée | SHA256 |
|---|---|
|round20/role4/attempt04.log|a9afe0af9956c7ac04e72f28d2eff2b802fb7fbfe71216b168da3929d92344db|
|round20/role4/attempt04_source_PREEXEC.lean.txt|1514baf7a4874b8f8c2919ca0c54c9b8a4d805fd41370b5b77aa5838e7a877d4|
|round20/role4/attempt04_started.json|35aa35a14397c20f898023e25d6be80c4fa426019a2e2a710e4df4eb6083c1ef|
|round20/role4/attempt05.log|983469c3ea1f7421c263c87c85abc3b21cdc3b39acf57845dbcf97ef2162fb22|
|round20/role4/attempt05_source_PREEXEC.lean.txt|df9ddafb7b497a286e7625ad27563b4610c6eb3cb22cc4a8dca3328f7e95d5d0|
|round20/role4/attempt05_started.json|0fe3ceb1ebf15e4b8f74142933d8d9ec2114df8ab273a058a8d0caab35e6fc29|
|round20/role4/attempt06.log|30ca2b190e6996bccf526a2229e60bbfca19a6e47fe2f6a4af1145e1dd675fb7|
|round20/role4/attempt06_source_PREEXEC.lean.txt|e85ae3005131de9c5689dc5da087846565c1d618009cdc5754fed94a3c36748d|
|round20/role4/attempt06_started.json|17580b93a4aec755cd700a08e567d2224b17e6158c4657975bf52118e8030882|
|round20/role4/attempt07.log|ba1900b1d98fa278b9f402f50118328812f34649342d50a81f50a148a7b11fa4|
|round20/role4/attempt07_source_PREEXEC.lean.txt|80051a67fa9d7bbc29c7766344a9fc7a02f483195b0696cfc70bf2556433d0a8|
|round20/role4/attempt07_started.json|17aa02391a88c0a95007747d8a9e9814e7e59e95f26b964337c67bdc7b50b711|
|round20/role4/FriablePhysicalPayment.lean|8b5884ad66ef853a072058c1058fe5ff96caf654a3337917b4378b82aeb26e1f|
|round20/role4/FriableTotientEnvelope.lean|4ed2263d8836eb05824df6a857801404d3f6ee7a1efd9b3cf57b087e837b01b0|
|round20/role4/FriablePrimeHarmonic.lean, dernière lecture FULL stable|7bc01aca55b63a4aa18f3c18d4d6e05fc9daf170cb951911f3e76c7933933b18|
|round20/agent2_friable.md, contexte FULL du rapport01|5635cff82cbd5e6e395dfef3617f8d2d89ead40f6dbbdfffa943bf0f6a785be5|
|round20/ideation_failure_feedback01.md, inchangé|562783b7999486ee57fcb66743c08cd52017c3694bca75a45c61198ec9be7d5f|

FULL sources04/06 : `471030`/`8feff8`; FULL logs04/06 : `5ed80f`/`51c664`; FULL START04/06 : `509f06`/`ac4a42`; registre04–07 extrait : `5d4fd2`. FULL sources05/07 : `75465e`/`fc8cc7`; FULL logs05/07 : `088653`/`fbf38d`; FULL START05/07 : `2cf9c0`/`84af8b`. FULL Payment : `5ad168`, hash avant lecture `c05372`, hash encore identique `4d3d2d`/`b4bfec`. FULL TotientEnvelope : `da1cfe`, hash `4d3d2d`/`b4bfec`. PrimeHarmonic a évolué pendant les lectures : première FULL `8bb226` et hash intermédiaire8e17e843 ne sont pas promus en version stable ; relecture FULL `e0267a`, hash7bc01aca identique avant/après. L’inventaire `cf6e3a` était tronqué et n’est pas revendiqué FULL. La provenance de FINAL2 demeure `db147b` dans le rapport01.
