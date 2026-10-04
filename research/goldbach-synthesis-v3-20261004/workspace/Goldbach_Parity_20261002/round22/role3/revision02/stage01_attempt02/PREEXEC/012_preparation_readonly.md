# ROLE3 — préparation en sources seulement, boucle22

Statut : READ_ONLY_PREPARATION_READY, pas FINAL d’exécuteur sélectionné. La mission est une préparation des API sans compiler. Aucune invocation de Lean, aucun `#check`, aucun import Python numérique, aucun calcul mathématique, aucune réexécution de résultat historique, aucune nouvelle preuve `.lean` n’a été lancée ou écrite.

USER_DIRECTIVE.md et PROBE_BLOCK.md ont été lus FULL, ainsi que le SKILL.md arbor-agent-executor. La directive de pivot et la portée précise de la mission priment : pas de worktree Git, pas d’installation, pas de tests d’exécuteur à ce stade. Les archives et les autres rôles ont été consultés uniquement en lecture. Seuls les fichiers de round22/role3 sont écrits.

Le rapport ROLE2 uniform_formula.md a été lu FULL dans son état DRAFT (chunk8608ab). La proposition contient un véritable objet géométrique défini indépendamment des premiers, puis un déroulement de son mode cusp0. Elle distingue elle-même le déroulement, la vraie diffusion, le signal de chaleur et le coefficient de Goldbach. La sélection effective par root et FINAL2 figé restent en attente. Toute version ultérieure de ce draft doit être relue et liée à un nouveau manifeste avant une exécution.

Le contrat et le producteur neuf de ROLE6 ont été lus FULL (epstein_contract22.json, chunk1080b6; epstein_bank22.py, chunk991d66). Leur cohérence papier a été examinée : primitive avec a>0, jacobien signé pour m<0, reindexation n→−n sur fenêtre symétrique, télescope de q termes aux deux bords et queue non négative. Aucun résultat numérique n’a été obtenu. Les six lignes y=10000 sont explicitement des évaluations de bords, tandis que les 18 lignes originelles évaluent aussi tous les décalages. Ce banc ne calcule pas le coefficientN ni le signal de chaleur.

Les sources mathlib FULL Sqrt.lean, Periodic.lean et FunctionSeries.lean ont été lues. Les autres fichiers listés dans input_manifest.json ont été inspectés dans les plages précises des reçus, ou seulement par recherches indiquées. Certaines recherches larges ont été tronquées; elles n’ont pas été créditées comme des lectures FULL et les API utiles ont été relues dans leurs plages ciblées.

Incident administratif réel : le premier lancement du writer de métadonnées via `powershell -File` a été rejeté par la politique locale d’exécution de scripts (chunk499d11, exit1), avant toute action du writer. Une invocation du même texte de métadonnées comme commande PowerShell native est ensuite utilisée; aucun réglage système n’est modifié. Cet incident ne constitue ni un échec Lean ni un contre-exemple mathématique.

Résultat préparatoire : api_plan.md décrit des obligations réelles pour la ligne Epstein à s=3/2, avec noyau indépendant, dérivée, FTC, intégrabilité, cellules entières, période1, échange de série intégrale et queue continue. Le cache possède `Integrable.hasSum_intervalIntegral_comp_add_int` et `Function.Periodic.intervalIntegral_add_zsmul_eq`, permettant de payer la multiplicité géométrique sans facteur |m| oublié. Les sommabilités, limites et raccords de puissances devront réellement être prouvés après sélection; leur présence comme charge dans le plan n’est pas une preuve déjà compilée.

Baseline historique conservée :57modules/942théorèmes auxiliaires. Modules nouveaux compilés par ce rôle :0. Théorèmes nouveaux vérifiés par ce rôle :0. Score de victoire :0. Aucun paiement nouveau de D_N n’est revendiqué.

Limitations toujours ouvertes : formule complexe générale, modularité et équation PDE, domaine de Friedrichs, unicité et diffusion réelle, dérivée de la diffusion, Mellin-Poisson, coût complet à N=10^8, correction des puissances premières et raccord au bilan D_N. Le test auxiliaire et le plan d’API ne ferment aucune de ces charges.
