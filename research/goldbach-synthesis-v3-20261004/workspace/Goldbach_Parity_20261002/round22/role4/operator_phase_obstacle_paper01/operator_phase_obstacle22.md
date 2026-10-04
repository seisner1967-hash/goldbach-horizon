# Réflexion additive et densité positive — PAPER01

**Résultat limité :** un opérateur positif de classe trace et son déterminant de Fredholm ne paient pas le signe de sa corrélation additive. Une identité concrète et une erreur de troncature sont dérivées ci-dessous ; aucune nouvelle loi signée suffisante pour D_N n’est obtenue. Note uniquement PAPER, sans Lean, probe, import, calcul, banc ni préparation runtime. Les nouveaux objets ne remplacent aucun test canonique ni acquis du ledger.

## 1. Objet continu concret, toutes puissances premières gardées

Fixer N entier≥6. Sur ℝ, poser φ(t)=(max(1−64t²,0))⁶ et A=∫φ². Ce réel est strictement positif et vérifie les bornes rationnelles fermées

`(3/4)^12/8 ≤ A ≤ 1/4`.

En effet φ≥(3/4)⁶ sur [−1/16,1/16], φ≤1 partout et son support est [−1/8,1/8]. Ses cinq premières dérivées se recollent à zéro aux deux bords ; φ est réelle, paire et C⁵. Définir son autocorrélation

`h_φ(s)=A⁻¹ ∫ φ(t)φ(t−s)dt`.

Elle est non négative, paire, supportée dans [−1/4,1/4], avec h_φ(0)=1. Ainsi h_φ(k)=0 pour tout entier k≠0. Définir `Bf(t)=A⁻¹/²∫φ(t−x)f(x)dx`. Cauchy–Schwarz pondéré puis Tonelli donnent `‖Bf‖₂≤‖φ‖₁‖f‖₂/√A≤‖f‖₂/(4√A)`. La parité de φ identifie B*B à la convolution par h_φ. Sa positivité est donc dérivée ; aucune classe trace n’est attribuée à cette convolution sur toute ℝ.

Dans l’espace réel L²(ℝ,dt), construire

`v_N(t)=A⁻¹/² Σ_(n=2)^(N−2) Λ(n)φ(t−n)`,

`R_N f(t)=f(N−t)`, `ρ_N f=⟨f,v_N⟩v_N`.

R_N est une isométrie autoadjointe, R_N²=I ; ρ_N est positif de rang≤1 et de classe trace. Aucun spectre de premiers n’est prescrit : v_N utilise la vraie Λ et toutes les puissances p^k dans la fenêtre. Les paires hors de [2,N−2] ont un partenaire0 ou1, de Λ nulle ; leur contribution à C_N est exactement nulle. La somme finie sert uniquement à définir son plongement continu, sans estimation de forme bilinéaire arithmétique.

Les intégrales de deux bosses sont exactement h_φ(n−m) et h_φ(N−n−m). La parité de φ, le changement t↦N−t et les échanges finis donnent donc

`Tr(ρ_N)=‖v_N‖₂²=Σ_(n=2)^(N−2) Λ(n)²`,

`Tr(ρ_N R_N)=⟨v_N,R_Nv_N⟩=C_N`.

Le coefficient extrait est le même C_N déjà payé par Fourier ; ce n’est pas un nouveau contournement. La nouvelle information utile est la séparation entre positivité de ρ_N et signe de sa composition avec R_N.

## 2. Obstacle démontré dans ce même espace

Choisir deux centres r et N−r séparés de plus de1/4. Le vecteur

`ψ=(φ(·−r)−φ(·−(N−r)))/√(2A)`

a norme1 et R_Nψ=−ψ. Sa densité ρ_ψ est positive, de classe trace, commute même avec R_N, mais `Tr(ρ_ψR_N)=−1`. Ce n’est pas un contre-exemple pour la vraie Λ : c’est une réfutation exacte de l’implication « densité positive + réflexion géométrique ⇒ trace composée positive ».

Même sur le cône des vecteurs non négatifs, aucun minorant strict universel ne suit. Les deux vecteurs de norme1 `u=φ(·−N/2)/√A` et `z=φ(·−(N/2+1))/√A` sont non négatifs. Leurs densités ont exactement le même spectre {1,0,…} et le même déterminant `det(I+sρ)=1+s`, tandis que leurs traces composées valent respectivement1 et0. Les seules données spectrales de la densité ont perdu sa position relative à la réflexion.

Avec P_±=(I±R_N)/2, toute corrélation réelle vérifie exactement

`⟨v,R_Nv⟩=‖P_+v‖²−‖P_-v‖²`.

Ce découpage géométrique ne désigne pas la parité du nombre de facteurs premiers. Poser une petite énergie P_- ou un écart positif suffisant en prémisse reproduirait le coefficient voulu ; aucune telle hypothèse n’est retenue. Construire plutôt `det(I+sρ_NR_N)=1+sC_N` remettrait seulement C_N dans un déterminant, sans l’estimer. Les orbites de zéros et leur conjugaison rendent le vecteur réel, sans supprimer son énergie dans P_-.

## 3. Contrat spectral auxiliaire avec erreur fermée, conditionnel explicite

Reprendre exactement χ_N(x)=s(2x−3)s(2N−3−2x) de la note signée, avec s′(u)=2772u⁵(1−u)⁵ sur [0,1]. Les bornes s′≤3 et |s″|≤55 donnent `|χ_N′|≤12`, `|χ_N″|≤512`. Le calcul direct de φ donne `|φ′|≤96`, `|φ″|≤8448`. Pour g_t(x)=χ_N(x)φ(t−x), l’opérateur D=x∂_x et la longueur de support≤1/4 donnent

`2‖g_t‖₁+2‖Dg_t‖₁+‖D²g_t‖₁ ≤ M_N`,

`M_N=[2+324N+11264N²]/4`.

Les hypothèses indépendantes encore nécessaires sont la vraie formule explicite μ(g)=B(g)−Z(g) sur ces tests C⁵, la bande0<Reρ<1 et les multiplicités/symétries complètes, ainsi que le comptage réel des zéros permettant

`Σ_(|Imρ|>H) 1/(1+(Imρ)²) ≤ Δ(H)=4(logH+1)/H+20/H²`, H≥exp(1).

Ce sont les charges annoncées dans signedWeil/orbit, pas des axiomes Lean ni une borne offerte sur D_N. Deux intégrations par parties en logx paient alors chaque terme par M_N/(1+γ²). Avec b(x)=1−1/[x(x²−1)], définir le vecteur fini véritable

`v_(N,H)(t)=A⁻¹/² [∫_(1,∞) b(x)g_t(x)dx − Σ_(|Imρ|≤H) ∫_(1,∞) g_t(x)x^(ρ−1)dx]`.

Le catalogue contient tous les zéros, sans RH, avec multiplicité et frontière ; sa stabilité par conjugaison rend v_(N,H) réel. χ_N vaut1 aux entiers de2 àN−2 et0 aux autres entiers pertinents : la formule explicite donne donc ce vrai v_N à la limite. Aucune série de zéros infinie pointwise n’est posée avant lissage. Le support en t est contenu dans [11/8,N−11/8], de longueur<N. La borne précédente construit ainsi, sans rayon libre,

`‖v_N−v_(N,H)‖₂ ≤ ε_N(H)=√(8N)(4/3)^6 M_N Δ(H)`.

Puis Λ(n)≤logN et la séparation des bosses donnent `‖v_N‖₂≤V_norm(N)=√(N+1)logN` ; ce normaliseur ne renomme pas le terme mixte L_N de Weil. L’isométrie R_N paie réellement

`|C_N−⟨v_(N,H),R_Nv_(N,H)⟩| ≤ ε_N(H)[2V_norm(N)+ε_N(H)]`.

Cette erreur est fermée et continue pour N≥6,H≥exp(1), tend vers zéro à N fixé, et son coût n’est pas masqué : ε_N a l’ordre symbolique N^(5/2)logH/H. Pour N=10⁸ il ne s’agit pas d’un producteur faisable annoncé. Une falsification demanderait le catalogue complet et des enclosures calculées de chaque intégrale, position, poids et primitive, comparées au coefficient canonique A32 et à son erreur déjà payée. Sans ces outputs : NOT_PREPARED. Aucun ε numérique libre ne suffit à attribuer un PASS.

## 4. Déficit exact conservé

Le ledger demeure `D_N=R_ref−C_N+Q_N+2max(e,0)−ε_tr`, avec Q_N des puissances propres, tous fronts/coins/unités et leurs conditions inchangés. La queue ci-dessus paie une approximation du joint trace ; elle n’apporte ni annulation de phase ni écart signé avec R_ref. Le contrat de signe manquant doit exploiter une propriété supplémentaire effectivement démontrée de la vraie ζ et de sa position relative à R_N, tout en transportant les correctifs du ledger. La positivité de ρ_N, ses invariants unitaires, les symétries d’orbites et le fond continu ne sont pas cette propriété. Aucun candidat de signe justifiable n’est retenu ; D_N et WIN restent ouverts.

Provenance : dn_gap_audit22.md51aea90f ; revue ROLE4orbit aeb411a7 ; revue JugesignedWeil4c356fc0, tous relus FULL361f28. Notes ROLE1signedWeil ab424c4b et orbit8cbca7b5 relues FULL8c6657. Leurs dettes de formule explicite/compte/extension ne sont pas promues en acquis. Aucune source gelée, banc04 actif, BORD04 ou Mellin37 n’est modifié. Les identités nouvelles et les bornes de cette note restent PAPER uniquement, sans nouvelle déclaration ni crédit officiel.
