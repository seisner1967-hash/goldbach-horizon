# Identity20 révision03 — diagnostic du vrai FAIL12

SOURCE_REVISION_NOT_COMPILED ; aucune compilation, probe, import candidate, parser, calcul, builder, préparation ou gate. Révision02 SHA533f81… et son lot12 restent immuables, comme original5b6da… et lots11/10. Envelope02 déjà indépendante PASS42 demeure readonly, sans recompilation.

Le seul enfant du lot12 a réellement commencé2026-10-03T15:58:01.295660UTC et fini15:58:25.178768UTC, exit1, aucun olean. Logf4cdc3f9f0ed4922a320a43230c5299e9c6319f065aff55ea5881d994eb01501 lu FULL3b3a0c ; reçu de20c1356084c9b048f258a7ddbbc14a08ca7a9037121c14bc42daef2d4385e3 et FIN8528baebc2a7eb1cd3e93391edd9f384aba38d4044c6c17b3ca1e784b2acf63f lus FULL311c5f. Une seule erreur de but non résolu, site43, treize prints standards et sept recovery sorryAx propagés ; aucun crédit module Identity. Les autres quatre sites précédemment corrigés n'ont aucune nouvelle erreur dans ce log. Ce constat est technique, sans conclusion d'obstruction analytique ou de parité.

But exact du log : exp(↑k*I*(2*↑pi))-1=0, alors que hperiod est exp(↑k*I*↑(2*pi))=1. La simplification finale ne normalise pas le type coercé de hperiod avant de l'utiliser. Le changement de preuve unique est

`simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hperiod`

après la construction existante de hperiod et avant l'intégration. Les deux lemmes réécrivent le produit réel casté et la constante2, sans modifier le coefficient entierk. Lecture API TARGETED363147 de Mathlib/Data/Complex/Basic.lean217–223 et423–429 :ofReal_mul(r,s), puis ofReal_ofNat(n)[n.AtLeastTwo], tous deux simp/norm_cast. Les lignes ne changent aucune hypothèse. Aucun nouveau théorème d'orthogonalité ni intégrabilité finale n'est ajouté en prémisse.

Nouvelle source8bb1eb5ec6ab4bf5e0c8cc053dcbe743049641dab5a3a3858205ad8ee2e2e9aa, FULLc0c3cf. Deux définitions/dix-huit théorèmes/vingt prints qualifiés écrits ; le contrôle est seulement textuel, pas élaboration Lean. Les vingt énoncés sont inchangés, finite a réel/M≥N et infini a>0, toutes les PP conservées. L'import de l'enveloppe doit provenir de ses bytes jugés77cdab/olean9c2bb947 ; cette source n'est ni recompilée ni importée par l'auteur.

Le prochain lot indépendant doit contenir uniquement Identity20 révision03 et Envelope readonly. Cette note ne crée aucune gate. L'étude PAPER NTT est suspendue ; les deux drafts circle_ntt_paper01/{exact_projection_contract22.md,native_algorithm_spec22.md} sont laissés sans modification, sans handoff final ou certification. H1spectraluniforme, évaluation numériqueN1e8, PP/front/D_N/WIN restent ouverts.
