# ROLE4 — échec réel Gamma1 et réparation source séparée

Une seule invocation Lean ROLE4 a eu lieu sous l'autorisation root1 SHA256 `c1bf99ded36a426e9bf0b741b3cdec6c329b353cdc0048b6671bafbba9e21e83`. START réel : `2026-10-03T07:49:03.589923+00:00`. FIN réelle : `2026-10-03T07:50:40.633827+00:00`. Sortie réelle : **1**, verdict `AUTHOR_GAMMA_H2_COMPILE_FAIL`. Aucun fichier olean n'a été produit. Les6392 liaisons immuables et3089 archives antérieures sont intactes avant et après. Les huit captures PREEXEC sont conservées dans gamma_attempt1/PREEXEC_FILES.

Source de l'essai : GammaPrerequisites22.lean, SHA256 `8bcfef577be2dbf3412646bd7938fe3d929dc0efdd4d1d7c29149ff6102ed7a0`. stdout SHA256 `3735c5ebe7fbfe53920bc03d47a5d1894422e4aab4557a61576490649911cf0f` ; stderr vide SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` ; reçu SHA256 `85f95efc916eb5de022ac8a4ca79f82d5d2df1c717cc1bf216fd2a927c80db45` ; START SHA256 `82410e4d5c1adde6ecac66960f98a7f5b558a65835e5e14d13054736edbf5f75`.

Le journal brut contient **six lignes error**, vingt-trois impressions d'axiomes, dont onze dépendent de sorryAx introduit par l'élaborateur après les erreurs. Les annonces intermédiaires de sept erreurs et quatorze audits affectés étaient des erreurs de comptage documentaire, corrigées ici. Aucun tel token n'était écrit dans la source. Les lectures FULL ROLE4 du journal et du reçu sont6c9b22/68e321 puis dd4411 ; ROOT les a lus FULL b1f5c1/5ad642. Le comptage correct du journal n'accorde aucune certification aux théorèmes dépendants des erreurs.

| Ligne originale | Erreur observée | Réparation rédigée dans revision01 |
|---:|---|---|
|79|Constante Complex.continuousAt_cpow_const inconnue|Utiliser continuousAt_cpow_const, globale dans le cache Pow/Continuity.lean83.|
|132|no goals après field_simp|Supprimer le ring redondant.|
|197|Exponentielles avec t*(-r) et -(r*t) non identifiées|Réduire explicitement les coercions et neg_mul avant commutativité du produit.|
|223|not a positivity goal pour 1<1+positive|Employer lt_add_of_pos_right avec la positivité du seul terme ajouté.|
|241|Réécriture du norm kernel sous applications lambda|Réduire les applications par dsimp only avant la réécriture.|
|293|no goals après field_simp|Supprimer le nlinarith redondant.|

Ces erreurs sont des incidents précis d'API, de normalisation et de tactiques ; aucune n'établit une contradiction arithmétique, un contre-exemple à l'identité de Laplace ou une nouvelle obstruction de parité. Le vrai H2 reste non certifié après cet échec.

La réparation est une source différente, revision01/GammaPrerequisites22.lean. Les déclarations, domaines et hypothèses sont conservés ; les preuves rédigées ne substituent aucune hypothèse libre à la vraie identité de Laplace ou à H2. L'original, préparations1–3, lanceurs1–3 et essai1 sont conservés sans mutation. La révision est SOURCE_ONLY : aucune seconde invocation, aucun nouveau banc ou rejeu n'est autorisé par le présent document. H1 Weil, le compte réel des zéros, Γ′ et sa domination, le raccord Stieltjes H3, le coefficient global et D_N restent ouverts.
