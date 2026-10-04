# Projection additive continue — SOURCE 01

Statut : SOURCE seulement, non PREPARED, non compilé. Dépendance directe : ThermalProjectionEnvelope22.lean, SHA3a348820aa1d2bd05eb5ceedc1f3c3d412ac6a0e3e4c9bf45c9e287f4d488aaa, également SOURCE. Aucun verdict numérique ou théorème final gratuit ne figure dans les prémisses.

Pour a>0 et N naturel fixé, T_a(theta)=Σ_n Λ(n)e^(-an)e^(in theta). Le module construit exactement

exp(aN)/(2π) ∫_0^(2π) T_a(theta) conjugate(T_a(-theta)) e^(-iN theta) dtheta
= Σ_(m=0)^N Λ(m)Λ(N-m).

Tous les poids de puissances de nombres premiers sont conservés. La corrélation a deux phases opposées avant conjugaison ; ses fréquences s'additionnent.

Les 20 déclarations (2 définitions et18 théorèmes) paient les étapes suivantes : caractère entier signé ; orthogonalité par vraie primitive exp(c theta)/c avec c≠0, et périodicité entière exacte ; conjugaison/fusion des phases ; annulation exacte e^(aN)e^(-aN) ; expansion finie et échange intégrale/somme par continuité effective de chaque terme ; filtre du rectangle identifié à l'antidiagonale lorsque M≥N ; coefficient en indice unique. Les étapes finies sont valables pour tout a réel.

Le passage à la vraie série exige a>0. Le module dérive B(a,M)→0 de (M+1)r^(M+1)→0 et r^(M+1)→0, r=e^(-a)∈(0,1). Le majorant pointwise indépendant de theta fournit une vraie convergence uniforme de T_M vers T. La borne déjà construite ||P−P_M||≤2exp(aN)AB donne la convergence des intégrales ; P_M est constant dès M≥N, donc l'identité entière suit de l'unicité de la limite. Aucun échange infini ni intégrabilité finale n'est supposé en entrée.

Lectures : source complète ; APIs ciblées du cache mathlib4.15 (intégrale exponentielle complexe, périodicité, conjugaison, sommes de produits/filter/map, antidiagonale, limites géométriques et Tendsto). La fermeture transitive, l'élaboration, les audits d'axiomes et une gate indépendante restent à établir. Les #print axioms écrits ne sont pas des sorties du compilateur.

Cette identité ne donne pas encore une évaluation zêta/spectrale uniforme en theta. La représentation continue via zêta pour toutes les phases, ses branches et son enveloppe numérique, les corrections canoniques de puissances de premiers, la frontière et D_N restent ouverts. Aucun contrat à epsilon libre, aucune minoration de Goldbach, aucun WIN. Le banc thermique actuellement en cours à theta=0 ne valide pas cette projection.
