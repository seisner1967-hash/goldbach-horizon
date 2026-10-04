# Boucle16 — rôle3 : marge eulérienne du premier manquant

**FINAL, production TERMINÉE.** Le nouveau module `role3/EulerAnchor.lean` compile sous Lean4.15.0, dernier essai13 exit0, sans erreur ni warning. Ses27 lemmes/théorèmes et huit définitions concernent le vrai produit singulier source ; leurs27 audits d’axiomes ne contiennent que propext, Classical.choice et Quot.sound. Aucun `sorry`, `admit`, nouvel axiome ou `native_decide` n’est présent dans le certificat final. Score0, victoryfalse : cette marge ne fournit aucune estimation d’incidence première ou de capacité globale.

## Énoncé effectivement certifié

`GoldbachRound16.Anchor.canonical_least_missing_prime_margin` prouve

`1/144 <= GoldbachRound11.singularSeries N - Real.log (leastMissingOddPrime N : ℝ)`

sous `N≠0`, `Even N` et l’input source acquis explicite

`2541/4096 <= GoldbachRound11.twinConstant`.

Les deux fonctions importées sont celles de `round11/lean/ThreeAdicPrimePairing.lean` : le twinConstant est le tprod réel sur tous les naturels, avec facteur1 hors des premiers impairs ; singularSeries utilise réellement les facteurs premiers de N, avec erase2 et le masque de parité. Aucun réel S libre ni hypothèse équivalente à la marge n’est substitué à ces définitions.

Le nouveau p0 est canonique. `leastMissingOddPrime N` utilise Nat.find parmi les vrais premiers impairs ne divisant pas N ; son existence est dérivée de l’infinitude des premiers. Sa spécification certifie la primalité, p0≠2, p0∤N et le fait que tous les premiers plus petits divisent N. N=0 possède un sentinel explicite et reste exclu des théorèmes. Le théorème paramétré précédent est plus fort : les facteurs premiers forcés suffisent à la marge, même sans utiliser ensuite p∤N.

L’enclosure C2 n’est pas redémontrée ni ajoutée comme axiome : elle reste une hypothèse déclarée sur l’objet réel acquis de la monographie, uniquement utilisée dans les quatre petits cas. Pour p≥13, la marge est dérivée sans cet input numérique.

## Chaîne de preuve réelle

1. Les facteurs twin sont dans[0,1]. Le net de tous les produits finis est antitone et minoré par0 ; sa convergence est dérivée par `tendsto_atTop_ciInf`. Le code ne suppose pas Multipliable et ne se sert pas de la valeur par défaut du tprod divergent.
2. Le produit eulérien fini `eulerPrefix p` est la somme convergente des réciproques des p-smooth naturels, par le théorème EulerProduct de mathlib appliqué au vrai homomorphisme n↦1/n. Les entiers1≤j≤p−1 s’y injectent : H_(p−1)≤eulerPrefix p est démontré.
3. Le produit entier sur k≤j<k+n est télescopé exactement : `(k−1)(k+n)/(k(k+n−1))`. Le même argument minore tout sous-produit fini à indices≥k. Pour k=p−1, la queue sur les vrais premiers est donc minorée par(p−2)/(p−1), et le passage à la limite réel est justifié par la convergence dérivée.
4. `twin_prefix_tail` certifie l’annulation des facteurs forcés : C2 multiplié par les facteurs locaux de tous les premiers impairs<p vaut le produit eulérien impair du préfixe multiplié par la queue réelle. Le facteur2 source est le facteur eulérien du premier2 ; les facteurs supplémentaires de N sont≥1.
5. La vraie série singulière vérifie donc `H_(p−1)*(p−2)/(p−1) <= singularSeries N` quand tous les premiers<p divisent N. Le module4 gelé `LeastMissingPrimeMargin.lean` apporte la marge harmonique pour p≥13. Les quatre petits cas3/5/7/11 utilisent les vrais préfixes finis et les logarithmes certifiés du même module4, avec l’enclosureC2 source.

Les27 lemmes organisent ces obligations de convergence, indices, annulation, bornes et sélection canonique ; ils ne représentent pas27 contrôles indépendants du résidu. Les neuf lemmes4 importés et les19+17 lemmes historiques ne sont pas recomptés dans le compteur27 de ce rôle.

## Tentatives Lean effectivement exécutées

Chaque tentative possède son propre snapshot et journal sous role3, lié dans build_receipt.json. Les anciens modules ne sont jamais reconstruits : leurs olean13 existants sont seulement lus. Aucun ancien banc numérique, gate, rendu ou PASS n’est réexécuté.

| Essai | Résultat réel | Diagnostic exact et correction |
|---|---|---|
|1|exit1, probe API|Quelques noms supposés de lemmes n’existaient pas. Les signatures effectivement disponibles sont lues ; aucun énoncé analytique n’est testé dans ce probe.|
|2|exit1|Réduction bêta du produit, commutation des inverses, coercition de l’injection de sous-types et syntaxe de branche d’induction. Corrections explicites des cibles et coercitions.|
|3|exit1|Dénominateur du télescopage non normalisé avant field_simp ; égalité `(k+n+1)−1=k+n` ajoutée. Le préfixe harmonique est déjà accepté avec axiomes standard.|
|4|exit0|Préfixe, convergence et télescopage acceptés. Deux warnings de style tactique, nettoyés lors de l’extension suivante.|
|5|exit1|Inférence du sup de Finset, focus dans un lambda, et normalisation p−1−1. Corrections de type et d’arithmétique.|
|6|exit1|`1+1` réel non réduit dans la queue finie ; norm_num explicite ajouté.|
|7|exit1|Simplification d’un if dans l’annulation des facteurs et nom indisponible d’un comparateur de produits. Passage au comparateur Finset.prod_le_prod. La queue infinie est déjà acceptée.|
|8|exit1|Le lambda du comparateur était inféré sur ℝ au lieu de ℕ ; domaine des indices annoté. L’identité twin_prefix_tail est déjà acceptée.|
|9|exit0|Raccord complet du vrai S à H fois la queue accepté, sans warning.|
|10|exit1|Les quatre petits préfixes n’étaient pas évalués par le simplificateur ; linarith voyait encore leurs produits. Les ensembles exacts∅,{3},{3,5},{3,5,7} sont certifiés par décideur kernel.|
|11|exit0|A7 paramétré complet, tous24 audits standard ; un warning de paramètre inutilisé dans un helper.|
|12|exit1|Dans la sélection canonique, change ne réduisait pas le if dépendant sur N=0. Le garde N≠0 est désormais utilisé via dif_neg. Le warning précédent est corrigé.|
|13|exit0|A7 canonique complet,27 audits standard, aucune erreur ou warning.|

Bilan :13 invocations compilatoires distinctes, dont un probe API et12 compilations du candidat ; neuf exit1 techniques et quatre exit0 sur des sources différentes. Les étapes intermédiaires PASS4/9/11 restent archivées avant leurs extensions ; le fichier final correspond exactement au snapshot13. Les journaux échoués contenant sorryAx décrivent les buts laissés par ces échecs et ne sont pas des certificats finaux. Aucun message Lean n’a identifié un blocage analytique de parité : l’obligation d’incidence demeure ouverte en dehors de ces preuves.

## Portée et prochain travail

A7 rend favorable le coefficient principal du vrai cœur premier p0 dans le domaine source quand le raccord U4 acquis est applicable. Ce module ne formalise pas de nouvelle disponibilité de q ou N−p0q premiers et n’ajoute pas un A9 sous hypothèse équivalente à son propre signe. La preuve de marge tient sans supposer une première incidence : une famille vide garde une capacité nulle.

Le contrôle de F6, des capacités après union, de la covariance corrigée TypeII et de tous les autres postes du ledger reste ouvert. Les kernels D/W réels, modèles S(bN), rawproperpowers, c1/e1/b1, cofacteurs longs, référence−S(N)N, originalalpha/Q, whole U_a, célibataires/faces/nonbulk, P5/K2 entier avant retrait et onset BV supplémentaire restent conservés. A7 est une avancée quantitative partielle pertinente ; aucun certificat de contournement du mur de parité pour D_N n’est revendiqué.

## Pièces gelées et environnement

Source final EulerAnchor.lean SHA `88bbbb4d8e49cf2906ec3ae06ec7a9f4bcaf6e08ee811733f090fb084fce0285`.
Import4 final SHA `e1dbd4f8a68b433c4641c90d6eb12366e7084b0d8b7b7b045b8b11ebd41e6b4a` ; rapport2 sélectionné SHA `f6f12c39afc445ce82482850c34482fa2450b9df1df7dbeef2089574b308128b`.
Lean4.15.0 et mathlib local commit9837ca9d65d9de6fad1ef4381750ca688774e608 ; huit bibliothèques déjà construites. `final_receipt.json` lie le rapport, le source, olean,13 snapshots/journaux, scripts et les imports lus. Tous les fichiers anciens701 restent intacts ; aucune mutation hors ownership role3 et ce rapport.
