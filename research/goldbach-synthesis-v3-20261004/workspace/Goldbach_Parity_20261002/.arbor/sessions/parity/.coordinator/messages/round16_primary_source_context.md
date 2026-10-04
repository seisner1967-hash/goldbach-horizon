# Contexte primaire vérifié par le coordinateur — boucle16

Lecture des premières pages du [PDF primaire Bennett–Martin–O'Bryant–Rechnitzer, Explicit bounds for primes in arithmetic progressions](https://arxiv.org/pdf/1802.00085), version3 du27 novembre2018, 103pages. Les équations1.10–1.11 et théorèmes1.2–1.3, pagesPDF3–4, donnent les constantes utilisées par le rôle1 : erreur de π_AP de taille x/(840log²x), erreur de θ_AP de taille x/(840logx), pour les modules3 et231 et x≥8·10^9. Chaque classe doit être unitaire ; chaque endpoint est contrôlé séparément. Le coordinateur a vérifié les énoncés, pas reproduit les calculs des appendices. Aucun résultat GRH supplémentaire n'est importé.

Le banc16 à N=10^8 a ses endpoints q≤3989 et candidats≤2·10^7, hors de ce seuil. Il teste les identités et les comptes exacts, sans appliquer ces estimations effectives. Le TypeI3 isolé ne donne ni le maximum complet des autres diviseurs ni les sommes TypeII du candidat.

Pour le rôle2, la source fournie et les définitions Lean existantes restent l'autorité du produit singulier. La formalisation sélectionnée doit dériver convergence, queue et passage Euler-harmonique du vrai produit ; l'enclosure C2 acquise est explicitement distincte de ces nouvelles obligations. La marge de coefficient ne démontre aucune disponibilité d'incidences premières.
