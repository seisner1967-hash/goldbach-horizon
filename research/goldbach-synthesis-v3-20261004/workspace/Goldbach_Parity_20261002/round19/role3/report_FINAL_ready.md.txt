# FINAL3 — prix de calibration de rang, node13.11

Six nouveaux modules ont un PASS auteur réel. 85 théorèmes explicites,23 définitions,108 prints d'axiomes standards ou aucun axiome. Aucun sorry/admit/axiome libre/native_decide/trustMe dans les sources compilées. Score0, victory=false ; le Juge indépendant n'a pas encore certifié ces résultats.

Le lanceur a exécuté 17 invocations Lean réelles :6 PASS et11 FAIL techniques. Chaque tentative conserve source, lanceur, gate, commande/environnement/imports PREEXEC, puis log/exit/reçu et chaque PASS olean préservé. Aucun ancien Lean/producteur, aucun PASS inchangé rejoué, aucune copie d'olean historique. Les quatre dépendances18 restent en lecture seule. La gate concrète lie le PASS numérique rank19 unique ; aucune production numérique par ROLE3.

| Module | PASS réel | Théorèmes | Définitions | Prints |
|---|---:|---:|---:|---:|
| RankCalibrationFace.lean | 3 | 19 | 3 | 22 |
| RankCalibrationPrice.lean | 5 | 24 | 7 | 31 |
| RankCalibrationArithmetic.lean | 8 | 16 | 3 | 19 |
| RankCalibrationUnitLoss.lean | 11 | 8 | 1 | 9 |
| RankCalibrationEuler.lean | 14 | 12 | 5 | 17 |
| RankCalibrationEstimator.lean | 17 | 6 | 4 | 10 |

Les trois warnings simpa de UnitLoss lignes25/26/29 sont bénins et conservés. Aucun module PASS n'est rejoué pour les supprimer. Les autres logs PASS sont sans warning.

Échecs réels et corrections :

- Face01 : réécriture de P dans les propres dépendances gcd/quotient ; decide ne réduit pas Squarefree1771.
- Face02 : réécriture de d dans ses propres gcd/quotients ; corrigée par congrArg₂ sur les seuls opérandes.
- Price04 : positivité de la branche U vide et cast2≤j alors que log_nonneg attend1≤j.
- Arithmetic06 : projection non bêta réduite ; déroulements concrets factorization/totient/divisors trop profonds ou non fermés.
- Arithmetic07 : trois norm_num superflus après rw totient_prime ayant déjà fermé les buts.
- UnitLoss09 : exact_mod_cast ne traverse pas le front rationnel vers le réel.
- UnitLoss10 : seule coercion du1 rationnel restait non simplifiée ; Rat.cast_one explicite.
- Euler12 : simplification de coprimalités/branches conditionnelles ne ferme pas les unités N et les deux termes IE.
- Euler13 : seule branche de coprimalité N positive reste ouverte ; split K et if_pos/if_neg explicites.
- Estimator15 : cast A≤J sans simplification de1*J ; chaîne calc triangulaire insuffisamment typée pour Trans.
- Estimator16 : inégalité finale devenue identique après simp only mais non fermée automatiquement ; le_rfl explicite.

Les prints des déclarations ratées utilisent sorryAx interne dans leurs logs d'échec ; ces tentatives ne sont pas des PASS. Les correctifs concernent élaboration, réécritures, calculs kernel et casts. Aucun contre-exemple à l'identité physique, aucun échec de parité n'est inventé à partir de ces erreurs techniques.

Face dérive l'exclusion sur le vrai PhysicalWitness18 de la face de trois petits premiers, le quotient P/gcd(P,d), les overlaps, le support A≤J' et la branche vide. Price conserve Gamma0=Gamma_rank+Eunit+Lrank, références réelles, theta/raw/properpowers et K6 avec le facteur A·lost/J. Arithmetic dérive les modules≤max(aR,R^4), la reconstruction squarefree d,k avec repeats et la multiplicité≤32 dans une expansion unique, ainsi que chi réel de totient et son minimum451/2336400. Ce lemme32 ne prouve pas le plafond combiné40/64 des trois développements.

UnitLoss dérive les seuls facteurs c/r>R perdus, les fronts+1 et une majoration de leur prix theta grâce au support physique. Euler conserve tous les diviseurs originaux, y compris Möbius nul, retire les seuls termes non unitaires à N arithmétiquement nuls, puis définit les restes effectifs. Estimator dérive l'identité exacte autour de −M·chi et sa borne triangulaire avec erreurs de normalisation et vrais restes. M est une expression réelle ; sa positivité effective n'est pas postulée ou démontrée dans cette portée.

K14 complet, positivité du coefficient IE effectif, raccord des restes unitaires aux AP ordinaires/endpoints et exceptions, multiplicité combinée source40/64, K17/K18 source, constantes/onset BV et application au seul logN≥10^24 restent ouverts. Gamma_rank peut augmenter du principal négatif opposé au prix ; aucune minoration de capacité ou petite Gamma n'est ajoutée comme prémisse. Comparaisons parents, autres familles, medium/longs, union physique des capacités et ledger entier restent impayés. La cible D_N≤N/(256logNloglogN) n'est donc pas prouvée.

Le cadre et les1361 archives restent inchangés. PREPARATION_REVIEW.md et preparation.json sont préservés. Le rapport3 était absent lors de la reprise ; le DRAFT nouveau est capturé dans agent3_DRAFT_PRE_FINAL.md.txt avant ce FINAL. La finalisation ne lit que les artefacts existants et ne lance ni Lean, ni producteur, ni Juge.
