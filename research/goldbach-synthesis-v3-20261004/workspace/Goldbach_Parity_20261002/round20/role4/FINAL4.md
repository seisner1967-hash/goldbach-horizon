# FINAL20 ROLE4 — coût friable physique au seuil source

Le théorème `actual_source_friable_absolute_cost_budget` a réellement compilé sous Lean 4.15 en Budget02, exit0, sans `sorryAx` et avec intégrité post-exécution inchangée. Depuis le seul seuil original `SourceOnset N`, soit `log N≥10^24`, il démontre

    sourceFriableAbsoluteCost N ≤ N/(8192*log N*log(log N)).

Ce coût est exactement la somme positive de `friableThetaDemand` sur le sous-domaine F0 ou F1 du véritable `physicalDomain`19 et de `uniqueReciprocalCost1` sur les réciproques F1 physiques fusionnés avant consommation. Ce paiement partiel ne prouve ni Goldbach, ni la cible globale D_N, ni un contournement complet de la parité. Le réciproque m1 nonfriable dans F0 privé de F1 demeure impayé.

## Clauses établies et objets utilisés

Les modules propres sont dans `round20/role4`. Ils importent les sources et oleans audités19/18/16/13 en lecture seule ; aucun ancien résultat n'a été recompilé ou recompté.

| Clause | Résultat formel effectivement établi | Modules |
|---|---|---|
| Ressources et certificat | Le cap réel et e>p0 donnent les deux ressources≥M. Le premier préfixe de `primeFactorsList`, avec répétitions, donne d divisant n et D≤d<DY. Couvertures, classes affines et impossibilités des nonunités sont raccordées au vrai H. | PhysicalPrefix |
| F1 | Vraies sommes friables de n^(sigma−1) et tau(n)*n^(sigma−1), tau=card des diviseurs, obtenues par sommabilité géométrique locale sur le fini des premiers. P-série -> Eminus -> somme des premiers≤3ell -> Eplus≤u^27 -> masse réelle du band≤u^−37 et cardinal≤DY fois cette masse. Aucune petite S_D n'est supposée. | EulerRankin, PrimeHarmonic |
| TK | L'identité n/phi(n)=somme des inverses de phi des diviseurs squarefree, l'Euler fini positif et le télescopage donnent uniformément somme_(1≤n≤X)1/phi(n)≤3(1+log X). `actual_TotientSumBound` décharge l'entrée indépendante du module KernelEnvelope. | TotientEnvelope |
| Kernel physique | Le complément court audité fournit C=Lambda(e)−mu(e)W, avec le vrai W et son log original. | KernelEnvelope |
| Axes ABS | ABS(C)≤7u² et vrais ABS(thetaBracket), ABS(rawBracket)≤7u³ sur H avec les gardes de rang. L'axe raw conserve les puissances propres et reçoit la borne directe de vonMangoldt ; aucun mu² n'y est introduit. | PhysicalDemand, PhysicalPayment |
| Classes et fronts | L'intervalle entier réel J_e, les classes des deux ressources et chaque +1 donnent une vraie couverture de F0 ou F1 et une borne de cardinal. Les nonunités impossibles portent zéro incidence active. | PhysicalPrefix, PhysicalPayment |
| F2 theta tous rangs | Les fibres finies couvrent toutes les strates de H ; le cutoff positif N/M est dérivé du cap. La somme complète est ≤14*u^−34*(N*H_(N/M)+(N/M)*D*Y). Tous les +1 sont dans le second terme. | PhysicalDemand, DemandAggregation |
| F3 unique | L'image en q fusionne tous les e avant le coût. q↦N−q est injectif, et les ressources m1 sont dans le vrai intervalle friable [M,N]. Le vrai sourceBracket est ≤7u³*tau(m1), puis le vrai tail Euler de tau donne U_F1≤7N*u^−39. | PhysicalPayment |
| Géométrie source | Floors/ceils originaux, Q exact, Ecap=(N−Q−1)/M et enlargement Eupper=N/M ; 25 gardes sont dérivées du seul onset10^24. Les wrappers donnent la masse source, le tail tau source et F3 source. | SourceGeometry, produit externe ROLE4_geometry |
| F4 du coût déclaré | Eupper*D*Y≤2N^(97/128)≤2N et H_Eupper≤u/2 donnent T_Ftheta≤8N*u^−33. F3≤N*u^−33 ; donc T_Ftheta+U_F1≤9N*u^−33≤N/(8192*u*ell). | SourceBudget |

La variante choisie pour l'agrégation et le budget est theta. La borne raw locale est également prouvée ; aucune agrégation F2 raw complète ni partition raw de Bpp n'est revendiquée. Les axes alternatifs ne sont pas ajoutés comme deux paiements. TK et les gardes géométriques sont déchargées dans le résultat source final, et aucune petite masse, demande ou capacité n'y est une prémisse.

## Périmètre mathématique restant

F0 privé de F1 a ses demandes couvertes par F2, mais son m1=N−q nonfriable n'entre pas dans F3. Une corrélation tau(N−q) avec la friabilité de N−p0*q ne suit pas de l'Euler univarié. Ces réciproques restent dans le ledger et la capacité originaux. La somme positive T_Ftheta+U_F1 surmajore le coût d'une union ; le présent Budget n'affirme pas une identité de partition du retrait ni un crédit de capacité pour une intersection.

Le bridge entre le domaine déclaré H19 et tout le support source reste distinct et ouvert. Le complément avec de grands facteurs, e=1/p0/singletons, les autres faces/nonbulk, Gamma/T_A, medium/long génériques, BV/onsets et la capacité totale restent impayés. Le ledger D_N original, ses S(b_N), −S(N)N, wholeU_a, Q/k1, P5 et l'alternative U4 sont conservés. Le nouveau coût ne s'ajoute pas à Iglobal comme bénéfice.

## Exécutions et artefacts

Les neuf modules propres ont demandé 22 invocations réelles : neuf PASS et treize FAIL techniques. Le dixième import SourceGeometry, produit par l'autre agent, a demandé deux invocations : un PASS et un FAIL. Total logique ROLE4 : dix modules, 24 invocations, dix PASS et quatorze FAIL techniques. Ces comptes excluent entièrement les anciens PASS. Aucun PASS n'a été rejoué.

Budget01 a commencé à 04:10:13.783046 UTC et échoué sur une seule positivité de dénominateur. Budget02, source corrigée, a commencé à 04:11:12.987596 UTC et fini à 04:11:42.316068 UTC, exit0. Sources PREEXEC, START, commandes, stdout, stderr, logs, codes réels et sorties olean sont conservés. Les nouveaux lanceurs d'extension vérifient également après compilation les imports gelés, gates, builders, ledgers, bindings numériques/historiques et runtime. Les logs PASS impriment uniquement `propext`, `Classical.choice`, `Quot.sound` pour les déclarations contrôlées.

Budget final : source SHA256 `9dd811fe823f50d8af08e4afa04f977011df4e01cf976df1fc663f9c85fceba4`, olean `4b680caaa8a26080557dd1188b55a125b78484644bb9c6909cd4c5065f1ed7a5`, ledger `ce9f0e0208f7d01346863c55848e322ca36bdc744ffa3c2da83dcbc21d74ac8c`, log02 `fb2157a4aa521413bf6ae8334630ae2a2542e3800afe2cf7427a247cb03fc4d7`.

Les détails des treize FAIL propres figurent dans `compiler_failures.md`. Ils concernent des tactiques, coercions, imports ou algèbre ; aucune erreur du compilateur n'est décrite comme une obstruction de parité. Les sources PASS et tous les artefacts de leurs tentatives sont gelés. La géométrie finale a été intégralement lue après publication de son PASS ; les portées de lecture antérieures partielles restent dans le reçu original, sans réécriture rétroactive.

Le banc neuf strict a été exécuté uniquement par ROLE6 et inspecté par la racine : ALL1001q avant masques, préfixes avec répétitions, kernels physiques theta/raw, 15 réciproques F1 uniques, quatre F0 privé de F1 nonfriables explicitement impayés, aucune décision float ou ambiguë. À N=10^8, Ysource=1 et les gardes source sont fausses ; Ytest=4096 est un test séparé. Les annexes Euler/TK finies ne sont pas une preuve du budget source. ROLE4 n'a exécuté aucun Python mathématique et n'a rejoué aucun banc.

Le manifeste final et le reçu final fixent les hashes des preuves et des exécutions. Le Juge indépendant peut contrôler ce paquet sous une nouvelle autorisation ; sa future évaluation n'est pas réputée exécutée. Verdict ROLE4 : F1–F4 de ce coût exceptionnel sont raccordés au seuil source, sans victoire globale.
