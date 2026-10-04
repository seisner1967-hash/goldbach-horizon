# Transport Mellin uniforme de la vraie phase thermique — SOURCE/PAPER 22

Statut : dérivation analytique sur papier, sans nouvelle compilation, import, parseur Python, calcul numérique, probe ou préparation de lancement. Ce document est distinct du paquet performance_sourcepack02 et de ses cinq outils launch_prepare03. Aucun de leurs fichiers ne change. Aucun crédit H1 global, coefficient N, D_N ou WIN.

Le premier déficit relevé par le Juge dans continuous_correlation_source_review22.md (SHA 04f40ed82430c203c8695180d7762a06a52bd5d0ce11a9657e80740e24e6f59c) est précis : la borne de Gamma au quart d'angle ne domine plus la puissance complexe lorsque |Arg(a-iθ)| dépasse π/4. L'identité de corrélation continue ne résout pas ce déficit. La proposition ci-dessous le paie par une rotation concrète dépendant de la fréquence verticale.

## Objets véritables et domaines

Pour a>0, θ réel, w=a-iθ, prendre Log(w) principal et w^{-s}=exp(-s Log(w)). La partie réelle positive évite zéro et la coupure du logarithme. Définir

T_a(θ)=Σ_{n≥1} Λ(n) exp(-an) exp(inθ),
L(s)=-ζ'(s)/ζ(s),
F_w(t)=Γ(2+it)L(2+it)w^{-2-it}.

Ici ζ est la vraie fonction zêta de Riemann et Γ la vraie fonction Gamma ; il n'y a ni trace abstraite ni facteur libre. Sur Re(s)>1, la non-annulation de ζ et l'égalité L(s)=Σ Λ(n)n^{-s} proviennent de la chaîne Euler réelle. Aucune inversion de Möbius, forme bilinéaire arithmétique, décomposition de Vaughan, crible ou estimation des progressions n'est employée.

La série T converge uniformément en θ à a fixé, puisque 0≤Λ(n)≤log n≤n et Σ n exp(-an)<∞. Elle est continue et 2π-périodique. Écrire

δ(w)=π/2-|Arg w|>0,
ρ=|w|>0.

Sur θ∈[-π,π], Arg(a-iθ)=-atan(θ/a), d'où δ(w)≥d(a)=atan(a/π)>0 et ρ≥a. δ et d sont des fonctions explicites continues sur leurs domaines, pas des rayons libres.

## Rotation déjà certifiée et majorant nouveau

La dépendance indépendante exacte est judge5/batch02_sources/GammaPrerequisites22.lean, SHA 9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7. Son théorème GoldbachContinuous22.Gamma_rotation_bound, lignes267–285, prouve pour σ>0 et |β|<π/2 :

|Γ(σ+it)|≤exp(-βt)(cos β)^{-σ} Γ(σ).

La preuve utilise la vraie identité Laplace à taux complexe, l'intégrabilité et la continuation analytique déjà payées. L'adjudication indépendante batch02 (SHA 6488a47dfb747394fbb16df8df7282ea660e7016c24e06753a7dad3f50519f02) atteste exit0, vingt théorèmes/trois définitions, vingt-trois impressions d'axiomes standards ; olean fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477. Aucune recompilation de cette dépendance n'a lieu ici.

Choisir maintenant β(t)=atan(t/2), qui satisfait strictement le domaine pour chaque t réel. Comme Γ(2)=1 et cos(atan(t/2))^{-2}=1+t²/4,

|Γ(2+it)|≤(1+t²/4) exp(-t atan(t/2)).

Pour t≠0, π|t|/2-t atan(t/2)=|t| atan(2/|t|)≤2 ; pour t=0, l'inégalité vaut directement. On obtient donc, avec une constante payée :

|Γ(2+it)|≤(t²+4)/4 · exp(2-π|t|/2).                      (G2)

Cette borne n'affirme aucune asymptotique de Stirling et ne suppose pas une décroissance gratuite au bord π/2. Le facteur polynomial provient exactement du choix atan(t/2).

Sur Re(s)=2, |L(s)|≤4. En effet log x≤2(sqrt x-1)≤2 sqrt x pour x≥1, par log y≤y-1 appliqué à y=sqrt x. Le test intégral monotone donne Σ_{n≥2} n^{-3/2}≤∫_1^∞ x^{-3/2}dx=2. Avec Λ≤log, on obtient Σ Λ(n)n^{-2}≤4. Par la formule exacte de la norme de la puissance principale,

|w^{-2-it}|=ρ^{-2}exp(t Arg w).

Ainsi

|F_w(t)|≤e² ρ^{-2}(t²+4) exp(-δ(w)|t|).                  (DOM)

Le déclin exponentiel restant est δ(w), explicite et strictement positif. L'aveuglement de la borne au quart d'angle est supprimé ; aucun résultat sur le coefficient additif n'en découle.

## Identité exacte et charges de preuve

L'identité candidate est

T_a(θ)=(1/(2π))∫_{ℝ} F_{a-iθ}(t) dt.                    (M)

Ce n'est pas une prémisse autorisée pour un théorème aval. Voici la dérivation proposée, qui indique les paiements encore à traduire en Lean :

1. Poser g(u)=exp(2u-exp u). Le changement x=exp u donne son intégrabilité, ∫g=Γ(2)=1, et sa transformée de Fourier dans la convention mathlib 2π : Fourier(g)(ξ)=Γ(2-2πiξ).
2. La borne G2 paie l'intégrabilité de cette transformée. L'inversion de Fourier, à u=log x avec x>0, puis t=-2πξ avec jacobien 1/(2π), donne e^{-x}=(1/(2π))∫ Γ(2+it)x^{-2-it}dt. La convention/signification du signe est fixée, sans inversion formelle non intégrable.
3. Pour w=a>0, sommer ce résultat en x=na. L'échange est réellement dominé par a^{-2} Σ Λ(n)n^{-2} ∫|Γ(2+it)|dt, fini grâce à G2 et à la borne4. Cela donne (M) sur l'axe réel positif.
4. Continuer les deux fonctions holomorphes en w sur Re(w)>0. Sur chaque compact, prendre b=min Re(w)>0, d=min δ(w)>0, et B=max |w|, tous issus du compact. La série et ses dérivées sont dominées par n e^{-nb} et n² e^{-nb}. L'intégrale et sa dérivée en w sont dominées par des polynômes explicites en |t| fois e^{-d|t|}, via DOM et le facteur (2+it)/w. L'identité analytique se prolonge par le théorème d'identité depuis l'axe positif.

Les APIs de Fourier d'inversion, de changement de variables et d'identité analytique doivent être appliquées à ces fonctions concrètes. Aucun intégrability/Fubini/analyticity libre ne remplace ces charges. Dans ce document, seule la rotation générale a le statut de dépendance Lean indépendante PASS ; M, G2 appliquée, DOM et les enveloppes qui suivent sont des dérivations PAPER, pas des théorèmes nouvellement compilés.

La périodicité appartient à T par sa série originale. Les intégrandes Mellin aux deux bouts θ=±π ne sont pas égales point par point. Leurs intégrales complètes sont égales par M ; les intégrales tronquées peuvent différer d'au plus deux fois la queue uniforme ci-dessous. Aucune périodisation artificielle du logarithme n'est supposée.

## Queue fermée continue

Pour H≥0, poser I_H(w)=(1/(2π))∫_{-H}^H F_w(t)dt. DOM et l'intégrale élémentaire de (t²+4)e^{-δt} donnent

|T_a(θ)-I_H(w)|≤E(w,H),
E(w,H)= e²/(πρ²) · e^{-δH} [(H²+4)/δ + 2H/δ² + 2/δ³].  (TAIL)

Tous les signes et le facteur 1/(2π) sont conservés : les deux demi-queues donnent le facteur2, puis l'intégrale t≥H produit exactement le crochet. Cette expression est fermée et continue pour Re(w)>0, H≥0.

Uniformément sur θ∈[-π,π], une enveloppe plus large mais explicite est

E_unif(a,H)=e²/(πa²)e^{-d(a)H}[(H²+4)/d(a)+2H/d(a)²+2/d(a)³].

Pour une garde η>0 imposée par un futur contrat, on peut payer une hauteur sans fixer librement une erreur de primitive. L'inégalité t²e^{-dt/2}≤16/d² implique

E_unif(a,H)≤C(a)e^{-d(a)H/2},
C(a)=e²/(πa²)(32/d(a)³+8/d(a)).

Le choix H(a,η)=2/d(a) · max(0,log(C(a)/η)) garantit la queue≤η. η est uniquement un budget demandé à cette queue et non une enclosure fictive de ζ, Γ ou d'une quadrature.

## Quadrature réelle sans majorant fourni en prémisse

Pour fermer aussi l'erreur de discrétisation analytique de I_H, utiliser la fonction holomorphe f_w(s)=Γ(s)L(s)w^{-s}. Autour de chaque point 2+ix, prendre le disque fixe de rayon1/2. Ce rayon vient du domaine Re(s)>1 et est payé par Re(s)≥3/2 sur le disque ; il n'est pas une hypothèse de rayon d'erreur.

Pour 3/2≤σ≤5/2, |L(σ+iv)|≤16 : log n≤4 n^{1/4}, puis Σ n^{-5/4}≤∫_1^∞ x^{-5/4}dx=4. Pour la vraie Gamma réelle, Γ(σ)≤3 : sur x∈(0,1), x^{σ-1}≤1 ; sur x≥1, x^{σ-1}≤x², et l'intégrale sur cette partie est au plus Γ(3)=2. La même rotation, β=atan(v/3), donne

|Γ(σ+iv)|≤3(1+|v|/3)³ exp(3-π|v|/2).

Poser Cρ=max(ρ^{-3/2},ρ^{-5/2}). Pour une cellule réelle de milieu x_j et largeur h_j>0, définir

u_j=|x_j|+h_j/2+1/2,
r_j=max(|x_j|-h_j/2-1/2,0),
M_j(w)=48e³ Cρ(1+u_j/3)³ exp(-δ r_j).

Cette valeur domine |f_w(s)| sur tous les disques de rayon1/2 centrés en 2+ix avec x dans la cellule. Cauchy donne |dF_w/dx|≤2M_j. L'intégrale de |x-x_j| vaut h_j²/4 ; pour S_K(w)=(1/(2π))Σ h_j F_w(x_j),

|I_H(w)-S_K(w)|≤Q(w,partition)=Σ M_j(w)h_j²/(4π).        (QUAD)

Chaque terme de Q est concret et continu en a,θ,H et les bornes de cellules, pour une partition fixée. L'enveloppe n'utilise pas de norme de dérivée ou de coefficient ζ fourni librement. Un choix uniforme K cellules de largeur2H/K donne aussi Q≤M_global(w,H) H²/(πK), où M_global=48e³Cρ(1+(H+1/2)/3)³. Cette dernière borne est volontairement grossière ; elle n'annonce aucune faisabilité.

## Contrat falsifiable proposé et coût symbolique

Pour M entier≥1 et r=e^{-a}, le témoin arithmétique fini est T_{a,M}(θ)=Σ_{1≤n≤M}Λ(n)e^{-nw}. Tous les Λ, y compris les puissances premières, doivent être produits à neuf par certificats arithmétiques ; aucune ancienne valeur du banc n'est un oracle. Λ≤n donne la queue concrète

B_M(a)=r^{M+1}[(M+1)/(1-r)+r/(1-r)²].

Une future banque indépendante compare la boîte de T_{a,M} et la boîte de S_K. Le budget analytique exigible est B_M(a)+E(w,H)+Q(w,partition). À cela s'ajoutent uniquement les rayons dirigés effectivement produits et vérifiés pour le témoin fini et pour chaque primitive Γ, ζ, ζ', exp, Log de S_K. Pour les termes Mellin, leur contribution est (1/(2π))Σ h_j ε_j avec ε_j égal au rayon effectif certifié du terme, jamais un paramètre libre. Le résidu des deux boîtes doit être compatible avec la somme complète de ces budgets. Une incompatibilité falsifie l'itération ; une compatibilité numérique reste auxiliaire.

Aucun producteur de ces nouveaux termes de Re(s)=2 n'est préparé ici. La preuve de leurs restes dirigés et le raccord aux enveloppes QUAD restent des obligations de formalisation/production distinctes avant toute autorisation de calcul. Les domaines des constantes, les facteurs1/(2π) et toutes les unités sont explicités.

Au choix N=10^8, a=1/N, d(a)=atan(1/(πN)) exactement, pas une valeur évaluée. Comme a→0+, d(a)~a/π, la hauteur garantie ci-dessus a un ordre symbolique a^{-1}(log(a^{-1})+log(η^{-1})). La constante de queue croît comme a^{-5}. La borne uniforme atteint donc des fréquences verticales d'ordre N log N lorsque le budget est fixé. Le nombre de primitives est K par phase, augmenté par les certificats du témoin M ; aucune mesure de temps, accélération ou succès à N=10^8 n'est inféré. La quadrature uniforme globale proposée peut imposer un K bien plus grand : c'est une dette pratique explicite.

L'amélioration réelle est une borne angulaire certifiable de la vraie fonction Gamma, avec une identité Mellin sur tout le demi-plan droit et une queue continue payée. L'étape suivante utile est la formalisation de G2/DOM/TAIL puis de M, et une quadrature adaptée réellement certifiée. Le passage aux zéros, les déplacements de contour, les composantes horizontales, la corrélation additive globale et le raccord bilantiel D_N restent ouverts. Aucun contournement du mur de la parité ni victoire n'est revendiqué.