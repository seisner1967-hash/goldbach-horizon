# Clôture réelle analytic02 — AUTHOR FAIL, 3 octobre 2026

Lancement unique `71e763`, session4665, FIN `1b99cc` exit1. Deux enfants Lean seulement : ΓBox PASS auteur (12 audits standards), puis ΓContour FAIL (trois lignes `error:`). Mellin et Inversion n'ont pas été invoqués. ΓBox doit encore être jugé indépendamment ; aucun crédit H1/C3/C5/D_N/WIN.

| Enfant | START → FIN UTC | Résultat |
|---|---|---|
| GammaBoxBounds22 | 11:26:43.257329 → 11:27:05.660191 | exit0, 12 audits standards, olean `4cb4d50f6d7dd8087e9d227d7052cb445527f018249dc3ffe6493ea2a87bfce3` |
| GammaContourComponent22 | 11:27:05.666576 → 11:27:29.293956 | exit1, 8 audits standards/3 sorryAx dus à l'élaboration, aucun olean |

Le batch a démarré à 11:26:43.241700 et son reçu s'est fermé à 11:27:37.767833. Dossier immuable : `analytic_batch02/actual_attempt01`. Reçu `d0bb6fda4cbdb187bea72c72423764a888c6a9cbd8ba87112e9d2519184dcbab`. PRE `a6709ff7333176ab165f8b8007c9578822a5a1d58f5cd3937b43538a6d7b83f9`, POST `8a9d3c0169f31e93136f9c76ec743aedcae0bc9a52adb522bda8e9312cbc148e` : 6524 inputs, 3089 archives et 24 captures intacts. ΓPrereq et ΓDerivative jugés sont des dépendances readonly, sans recompilation.

Diagnostic précis : ligne61:26, `ContinuousAt.comp` infère une addition appliquée au mauvais argument ; les deux fonctions composées doivent être typées explicitement. Ligne87:6, `Real.integral_exp_neg_Ioi` est inconnu, puis la réécriture échoue en cascade. Lecture TARGETED `01a14e` d'ImproperIntegrals.lean lignes1–57 : le vrai théorème est dans le namespace racine, `integral_exp_neg_Ioi`, sans préfixe Real ou MeasureTheory. Ce sont des erreurs d'élaboration/API ; aucun contreexemple analytique n'est établi.

Lectures FULL : logs enfants, START/FIN, reçu et POST `0f7e60` ; PRE seul `f0b315`, START batch `867efe`. Le PRE dans la sortie agrégée0f7e60 était tronqué et n'est pas crédité FULL. stdout Box `a0101541a42f02a38c9cd55cfff4a8c5ce2e0e8e0b4e213e73dd6e7e12998c7d`, stdout Contour `1e72a122b34680b073571e620e16125e55ce4a7b6c20ed43fdd62128bd588510`.

Total ROLE4 : sept invocations Lean réelles, aucun retry implicite. Ce rapport neuf ne modifie aucun paquet/capture/gate antérieur. Priorité ROOT suivante : revue et sources du contrat numérique global H1 à N=10^8 ; aucun nouveau batch auteur ni calcul n'est lancé.
