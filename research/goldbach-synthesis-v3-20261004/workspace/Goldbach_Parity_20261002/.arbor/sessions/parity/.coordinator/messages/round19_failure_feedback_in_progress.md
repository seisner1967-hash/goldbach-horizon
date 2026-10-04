# Retour19 en cours aux prochaines idéations

Les rôles d'idéation19 ont terminé et leurs handles sont déjà réapés. Ce retour durable sera transmis intégralement à la prochaine vague ; il ne modifie pas les FINAL1/2 figés. Les acquis et les1361 archives restent inchangés.

La première invocation réelle Lean19 sur TerminalPrimeExtraction a terminé exit1. Le compilateur a refusé trois preuves : fonction `id` non inférée dans `Finset.le_sup` (ligne29), positivité manquante pour `Nat.div_self` (ligne70), recursion maximale de la tactique sur une factorisation concrète (ligne120). Les déclarations ratées affichaient `sorryAx` interne ; elles n'ont pas été acceptées. Aucun `sorry`, `admit` ou axiome n'a été ajouté au source. Les corrections explicites ont donné un PASS auteur à la tentative02, à confirmer par le Juge. Ces refus ne constituent pas un contre-exemple arithmétique ni une estimation de parité.

Un incident séparé du lanceur Python a précédé toute invocation Lean : syntaxe invalide de `entry.update`, conservée avec une capture POSTEXEC honnête et le log réel. Sa réparation n'est pas comptée comme échec Lean. La tentative03 Balanced a ensuite réellement échoué sur la décidabilité du sélecteur et l'élaboration des fronts Nat.sub ; le rôle4 conserve ses captures et effectue une réparation technique. Les reçus finaux donneront les comptes exacts de toutes les tentatives.

Le nouveau test non-SS a un unique PASS fini, sans relance. Il confirme précisément pourquoi aucune simplification gratuite ne paie le ledger : répétitions h/r non coprimes, canal P dont les deux autres formes sont composites, conducteur dépassant sqrtN, triprime réciproque à bracket positif, ressource répétée à Möbius nul, et même m1 partagé entre plusieurs e. Les vraies définitions D/P conservent ces cas. Le test ne falsifie pas l'identité proposée ; il falsifie six promotions supplémentaires.

Le blocage mathématique restant est distinct des erreurs techniques : H4 est une réindexation avec prix signés conservés ; aucune estimation des canaux medium/longs, de tous les rangs et de la capacité physique unique n'est démontrée. Le prix de rang conserve Gamma_rank et ses restes AP effectifs. K14, la positivité du coefficient IE effectif, K18-source et les onsets ne sont pas encore raccordés en Lean. Une compilation auxiliaire ne satisfait donc pas la condition de victoire.


## FINAL4 : tous les échecs réels conservés

Tentative 01 TerminalPrimeExtraction exit1, log SHA ab7a7d1dd17daedda6d122b8aba515067d96b650a9ad895e73939d80878c8b42. type mismatch ; unsolved goals ; tactic 'simp' failed, nested error:

Tentative 03 BalancedResourceSwitch exit1, log SHA a51fa4ff3709c1298b0a61d962e10ddc5d788774ea6444f092373cf8f34fcfbe. failed to synthesize ; omega could not prove the goal: ; unsolved goals ; unsolved goals ; unsolved goals ; unsolved goals ; omega could not prove the goal: ; linarith failed to find a contradiction ; unsolved goals

Tentative 04 BalancedResourceSwitch exit1, log SHA 3661596e844def8c7a72eaf3df889c401503d28376a056d76496938bad54949f. omega could not prove the goal: ; unsolved goals

Tentative 06 SignedHyperbolicCRT exit1, log SHA 8093ac5437153375a9cf33eef17ab6d6afd3c56c93bcd86cc93d9183e185bfa9. invalid 'by' tactic, expected type has not been provided ; unsolved goals ; unsolved goals ; unsolved goals

Tentative 08 NonSSBracketSwitch exit1, log SHA 5269bdb8ec8a6f04d4c7ce60167e279307aae26316b93da0961bf2425b85185f. invalid field notation, type is not of the form (C ...) where C is a constant ; ambiguous, possible interpretations ; invalid field notation, type is not of the form (C ...) where C is a constant ; ambiguous, possible interpretations ; invalid field notation, type is not of the form (C ...) where C is a constant ; ambiguous, possible interpretations ; invalid field notation, type is not of the form (C ...) where C is a constant ; ambiguous, possible interpretations ; invalid field notation, type is not of the form (C ...) where C is a constant ; ambiguous, possible interpretations ; simp made no progress ; simp made no progress ; simp made no progress ; tactic 'apply' failed, failed to unify ; tactic 'apply' failed, failed to unify ; tactic 'rewrite' failed, did not find instance of the pattern in the target expression ; omega could not prove the goal: ; tactic 'rewrite' failed, did not find instance of the pattern in the target expression ; tactic 'rewrite' failed, did not find instance of the pattern in the target expression

Tentative 10 RankTwoHarmonic exit1, log SHA 6f1673886d6c572df47667f9814e18c2c8efc881505726cf4c83ed3d13359b75. tauto failed to solve some goals. ; unsolved goals ; unsolved goals ; no goals to be solved ; tactic 'rewrite' failed, did not find instance of the pattern in the target expression

Tentative 11 RankTwoHarmonic exit1, log SHA acb8b8bdd6ad488182c39387184d2e051d3007abdac2d9f0b6f2ece4425698c2. unsolved goals

Ces sept FAIL sont des erreurs de formalisation réparées, pas une preuve de petit résidu. Les cinq PASS prouvent seulement la reindexation/support et H8 exact. H7/H9, onset source, medium/long, Gamma, capacité et ledger entier restent impayés.


## ROLE3 : premières tentatives réelles

Tentative 01 RankCalibrationFace exit1, log SHA9554e10bee9ba615aec909a114ad73839f28278ce646d8ff3dc1423b99b34e45 : unsolved goals ; tactic 'decide' failed for proposition

Tentative 02 RankCalibrationFace exit1, log SHA5a2b0e0e4c548b7c7a58ccf17564813b4662077db70049d1d520e4cc172e1519 : unsolved goals

Tentative 04 RankCalibrationPrice exit1, log SHA7c6b4d90fa668ee466f79c4ac7774f54e2dbd7f6bb01584eb3360c84c7e054a3 : unsolved goals ; mod_cast has type

Face03 PASS corrige les réécritures dépendantes par congrArg₂ et prouve le carré-libre par les trois facteurs effectifs. Price04 demeure une erreur de branche vide et de cast 2≤j vers 1≤j ; aucun petit prix ou Γ favorable postulé.


## FINAL3 : onze échecs techniques effectivement conservés

Tentative 01 RankCalibrationFace exit1, log SHA 9554e10bee9ba615aec909a114ad73839f28278ce646d8ff3dc1423b99b34e45. unsolved goals ; tactic 'decide' failed for proposition

Tentative 02 RankCalibrationFace exit1, log SHA 5a2b0e0e4c548b7c7a58ccf17564813b4662077db70049d1d520e4cc172e1519. unsolved goals

Tentative 04 RankCalibrationPrice exit1, log SHA 7c6b4d90fa668ee466f79c4ac7774f54e2dbd7f6bb01584eb3360c84c7e054a3. unsolved goals ; mod_cast has type

Tentative 06 RankCalibrationArithmetic exit1, log SHA a4a93554147c04b6a3ba9fb068da8468e5c1882148402413cddc696b98f3eb3a. tactic 'rewrite' failed, did not find instance of the pattern in the target expression ; tactic 'simp' failed, nested error: ; unsolved goals ; maximum recursion depth has been reached ; unsolved goals

Tentative 07 RankCalibrationArithmetic exit1, log SHA 9d80d4cf6fdf2f99d9435c216c7196ce58a6e647fabf350604310e00ba870184. no goals to be solved ; no goals to be solved ; no goals to be solved

Tentative 09 RankCalibrationUnitLoss exit1, log SHA edd5e05f692b299deb113d186b329c66d1a546b0697a0eab8443f0c718990e6e. mod_cast has type

Tentative 10 RankCalibrationUnitLoss exit1, log SHA 26ddb9526719a745acca9ac9b0cfd2242d8ae718a01bb1f807d115da5cb736b0. type mismatch, term

Tentative 12 RankCalibrationEuler exit1, log SHA 38f072f416a54ab077762059aa9777368a6fd223778d00a5100cd8efb79ae58c. unsolved goals ; unsolved goals ; unsolved goals

Tentative 13 RankCalibrationEuler exit1, log SHA 8ea8474e4720776873d7eebe9ba99fb4fbce545418238f5b691a66f1b43a5156. unsolved goals

Tentative 15 RankCalibrationEstimator exit1, log SHA 458aa29d1f35e24a8153a463230adc85d910f58c3096718a7b56cc33813c9a02. mod_cast has type ; invalid 'calc' step, failed to synthesize `Trans` instance

Tentative 16 RankCalibrationEstimator exit1, log SHA bd677b6b5fe28a8e36649e8ae6e54378e1803fa4544916cfaf9172279e7e740f. unsolved goals

Aucun de ces FAIL techniques ne prouve un obstacle arithmétique. Les six PASS sont auxiliaires ; K14/source AP/K18/Γ_rank/capacité/ledger entier restent ouverts.
