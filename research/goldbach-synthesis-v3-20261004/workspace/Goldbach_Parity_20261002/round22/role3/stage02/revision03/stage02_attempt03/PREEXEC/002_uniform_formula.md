# ROLE2 / boucle22 — identité et enveloppe uniforme proposées

Statut : PAPER_ONLY, zéro invocation mathématique, numérique ou Lean. Proposition pour sélection par root, aucune victoire, aucun résultat formel nouveau. Les formules de cette note sont des dérivations sur papier à vérifier, non des hypothèses admises dans Lean. La Laplacienne, le canal de diffusion, le mode cusp0, la trace complète et le coefficient de Goldbach sont des objets distincts.

## 1. Géométrie indépendante du résultat recherché

Soit X=PSL(2,Z)\H, mesure dA=y^(-2)dxdy. Sur L²(X,dA), partir de Δ0=−y²(∂x²+∂y²) sur les fonctions lisses à support compact du quotient orbifold. Le domaine de la forme de Friedrichs est la fermeture pour ||f||²+q(f), q(f)=∫(|∂xf|²+|∂yf|²)dxdy. Le domaine opérateur est {f dans ce domaine de forme : il existe g dans L², q(f,h)=<g,h> pour tout h}; Δf=g. Densité, fermeture et représentation de cette forme constituent de vraies obligations de preuve. X, sa métrique et Δ ne contiennent ni N, ni primalité, ni D_N.

L'opérateur complet possède un continuum; sa trace thermique ordinaire n'est pas utilisée et n'est pas déclarée trace-class. Le mode constant, les modes cuspidaux et résiduels ne sont pas supprimés. On construit seulement le canal d'onde constante dans le cusp, puis son coefficient scalaire de diffusion. Un déterminant sur ce canal de dimension1 n'est ni un déterminant Fredholm de la résolvante complète, ni une trace de Birman–Krein d'une paire non construite.

Pour z=x+iy, y>0, Re(s)>1, poser

E_full(z,s)=(1/2) Σ_(m,n)∈Z²\{(0,0)} exp(s log y −s log(|mz+n|²)).

Les logarithmes de y et de |mz+n|² sont réels, car ces bases sont strictement positives. Aucune puissance complexe ambiguë, aucune série de 1/ζ, aucune inversion Möbius, aucun totient n'intervient. Définir E=E_full/ζ(2s) seulement là où ce dénominateur est non nul. La normalisation fixe le coefficient entrant à1. La convergence locale uniforme et ses dérivées, la modularité par changement entier de coordonnées et ΔE=s(1−s)E restent à formaliser.

Le mode cusp0 est calculé directement. Les termes m=0, n≠0, avec le facteur1/2, donnent exactement ζ(2s)y^s. Pour m≠0, la substitution u=mx+n transforme les intervalles [n,n+m]; leur recouvrement a multiplicité |m| presque partout, compensant le jacobien1/|m|. La série absolument convergente permet l'échange intégrale/somme. Donc

∫_0^1 Σ_n [(mx+n)²+(my)²]^(-s)dx
=∫_R [u²+(my)²]^(-s)du
=sqrt(π) Γ(s−1/2)/Γ(s) ·(|m|y)^(1−2s).

La dernière intégrale se déduit de l'intégrale gamma et de Tonelli/Fubini, avec Re(s)>1/2; elle n'utilise aucune élimination de facteurs premiers. La paire m et−m absorbe l'autre facteur1/2. Ainsi, avec A(s)=sqrt(π)Γ(s−1/2)/Γ(s),

C0 E_full = ζ(2s)y^s+A(s)ζ(2s−1)y^(1−s),
C0 E = y^s+φ(s)y^(1−s),
φ(s)=A(s)ζ(2s−1)/ζ(2s).

Le passage de cette solution géométrique au VRAI coefficient de diffusion nécessite encore la résolvante de Δ et l'unicité de la solution normalisée. Pour Re(s)>1, s(1−s) est négatif si s est réel, non réel sinon; cette région appartient à la résolvante d'un Δ positif auto-adjoint. Il faut également contrôler que la différence de deux solutions ayant les mêmes données cusp est dans le domaine approprié. La formule méromorphe historique n'est pas transformée en axiome. La preuve divisorielle Möbius/totient de Cakoni–Chanillo est explicitement exclue.

Sources primaires : [Lagarias–Suzuki, équations(1),(2),(10),(11), pages1–2](https://arxiv.org/pdf/math/0412039), pour le vrai Epstein non primitif et son mode constant; [Borthwick, pages24,35–38,63](https://math.dartmouth.edu/~specgeom/Borthwick_slides.pdf), pour Friedrichs, Eisenstein et le canal de diffusion; [Cakoni–Chanillo, §2](https://sites.math.rutgers.edu/~chanillo/te.pdf), pour l'énoncé de diffusion, sans reprendre sa preuve Möbius.

## 2. Isolement arithmétique global exact

Poser L(w)=−ζ'(w)/ζ(w), ψ=Γ'/Γ et, Re(w)=2,

D(w)=(1/2)[ψ(w/2)−ψ((w+1)/2)−φ'/φ((w+1)/2)].

La dérivation du quotient donne D(w)=L(w)−L(w+1). Par télescope, pour tout K naturel,

L(w)=Σ_(0≤k<K) D(w+k)+L(w+K).

Ce télescope est une identité analytique de diffusion globale. Il ne constitue ni une identité bilinéaire arithmétique locale ni un crible. Pour Re(w)≥2, ζ(w)≠0 se prouve même sans Euler/Möbius : |ζ(w)−1|≤1/4+∫_2^∞x^(-2)dx=3/4, donc |ζ(w)|≥1/4. Tous les facteurs gamma de la ligne utilisée sont réguliers.

Pour σ≥2, définir la fonction réelle continue explicite

C(σ)=log(2)·2^(−σ)+2^(1−σ)[log(2)/(σ−1)+1/(σ−1)²].

De Λ(n)≤log n, la décroissance de log(x)x^(−σ) sur [2,∞) et l'intégrale élémentaire : |L(w+K)|≤C(2+K). C'est une queue dérivée sur tous les entiers, non une borne de D_N postulée. Le terme gamma de D est conservé. [NIST DLMF27.4.12](https://dlmf.nist.gov/27.4.E12) donne la série de L; [DLMF5.7.6](https://dlmf.nist.gov/5.7.E6) fixe la fonction ψ.

Pour Re(t)>0, avec Log principal, définir le signal global

F(t)=Σ_(n≥2)Λ(n)e^(−nt)
    =(1/(2π))∫_(y∈R)Γ(2+iy)L(2+iy)t^(−2−iy)dy.

L'intégrale est absolument convergente. Pour K≥2, L_K(w)=Σ_(k<K)D(w+k) et

P_K(t)=(1/(2π))∫ Γ(2+iy)L_K(2+iy)t^(−2−iy)dy
      =Σ_(n≥2)Λ(n)(1−n^(−K))e^(−nt).

En particulier |F(t)−P_K(t)|≤C(K), uniformément sur tout Re(t)≥η>0. Ce majorant direct est plus fort que la borne Mellin B(η)C(K+2) mais n'en remplace pas la justification. Toutes les puissances premières sont conservées dans Λ; aucune restriction aux carrés-libres n'est introduite.

## 3. Enveloppe continue fermée pour Mellin et son échantillonnage

Sur le rectangle t=η−iθ, |θ|≤π, 0<η≤1, poser

δ=π/2−arctan(π/η)>0,
B(η)=η^(−2)(10+24/δ³)/(2π).

Identités gamma exactes : |Γ(2+iy)|²=(1+y²)π|y|/sinh(π|y|), avec la valeur continue1 en0. Donc |Γ(2+iy)|≤1 pour |y|≤1 et ≤6y²e^(−π|y|/2) pour |y|≥1. Les constantes suivent de π<4 et de la récurrence gamma; il n'est pas utilisé d'asymptotique avec constante implicite. [DLMF5.4.3](https://dlmf.nist.gov/5.4.E3), [DLMF5.5.1](https://dlmf.nist.gov/5.5.E1) et [DLMF2.5.2](https://dlmf.nist.gov/2.5.E2).

Une troncature intégrale |y|≤T, T≥1, a erreur ≤

E_T=(6/π)C(2)η^(−2)e^(−δT)(T²/δ+2T/δ²+2/δ³).

Le petit δ sur le bord du contour est obligatoire. La valeur δ=π/2 de l'axe réel ne peut servir pour tout θ.

Une option évitant une erreur de quadrature libre consiste à prouver Poisson sur la fonction SCHWARTZ v↦e^(2v)P_K(t e^v). Son caractère Schwartz suit des séries absolument convergentes, de leurs dérivées et des bornes de chaleur ci-dessous; ce point n'est pas remplacé par la version «outline» de Poisson dans une référence numérique. Pour h>0, a=2π/h et q=e^(−a), l'identité exacte est

(h/(2π))Σ_(j∈Z) Γ(2+ijh)L_K(2+ijh)t^(−2−ijh)
=Σ_(l∈Z)e^(2al)P_K(t e^(al)).

Le terme l=0 vaut P_K(t). Pour les autres termes, Λ(n)≤2sqrt(n), obtenu par log n=2log sqrt(n)≤2(sqrt(n)−1), entraîne

|P_K(s)|≤2[(Re s)^(−3/2)+(Re s)^(−1)].

Pour Re(s)≥1, l'autre majorant |P_K(s)|≤4e^(−Re s) est valable. Si ηe^a≥4a et a≥log2, les alias Mellin sont donc payés par

A_Mellin=2η^(−3/2)q^(1/2)/(1−q^(1/2))
          +2η^(−1)q/(1−q)+4q²/(1−q²).

Le dernier terme se déduit de ηe^(al)≥4al pour tout l≥1. Tous les dénominateurs sont strictement positifs. Ces formules sont continues dans η et h sous leurs gardes.

Pour la somme numérique finie |j|≤J, avec (J+1)h≥1, b=e^(−δh) et j0=J+1, le vrai reste discret est

E_J=(6C(2)/π)η^(−2)h³ b^j0
    ·[j0²/(1−b)+2j0 b/(1−b)²+b(1+b)/(1−b)³].

Le facteur1−n^(−K) permet |L_K(2+iy)|≤C(2). On ne paie pas chaque rang K indépendamment. Poser finalement

epsilon_F=C(K)+A_Mellin+E_J+epsilon_eval.

epsilon_eval est le rayon réel certifié de toutes les évaluations gamma, ψ, φ'/φ, puissances et de la somme; il doit être construit par intervalles à arrondi dirigé. Il ne peut être déclaré petit. L'intégrale gamma, le déroulement cusp et l'identité Mellin-Poisson ont leurs propres obligations formelles. Référence numérique primaire pour le mécanisme Poisson/trapèzes : [Trefethen–Weideman, §5, équations(5.8),(5.9)](https://people.maths.ox.ac.uk/trefethen/publication/PDF/2014_149.pdf); notre version utilise des hypothèses Schwartz à prouver et sa queue explicite, non leur argument «outline» pris comme axiome.

## 4. Coefficient global N et coût de son extraction

G_N=Σ_(1≤n<N)Λ(n)Λ(N−n) est un observable brut DISTINCT de D_N. Exactement,

G_N=e^(ηN)/(2π)∫_(−π)^π F(η−iθ)² e^(−iNθ)dθ.

Ce raccord analytique est une extraction générique; il ne constitue pas à lui seul un nouvel estimateur spectral ni un contournement établi. Son seul nouveau contenu candidat vient du producteur géométrique de F, construit indépendamment du coefficient cible.

Pour un quadrillage COMPLET de M entiers M>N, θ_j=2πj/M et F approché avec erreur uniforme epsilon_F, la quadrature au cercle a un vrai repliement, payé explicitement. Avec r=e^(−η), x=e^(−ηM), B_F=r/(1−r)², les coefficients supérieurs satisfont G_l≤(l³−l)/6≤l³/6. D'où

A_circle=(1/6)[N³x/(1−x)+3N²M x/(1−x)²
          +3NM²x(1+x)/(1−x)³+M³x(1+4x+x²)/(1−x)^4].

Les termes alias sont exactement G_(N+lM)e^(−ηlM), l≥1. L'absence d'alias négatifs exige M>N. Pour l'estimateur numérique complet G_hat,

|G_N−G_hat|≤e^(ηN)(2B_F epsilon_F+epsilon_F²)
              +A_circle+epsilon_outer_round.

L'amplification e^(ηN) et epsilon_F² ne sont pas oubliées. À N=100000000, le contrat complet proposé prend η=8logN/N, M=N+1=100000001, K=512, h=1/128, J=1280000000000 (hauteur J h=10^10). Il faut certifier les enveloppes et les rayons, sans résultat numérique déjà calculé. Le coût théorique est astronomique : 100000001 signaux, chacun de 2560000000001 nœuds Mellin avant toute accélération prouvée; les (K−1) appels de diffusion supplémentaires aggravent encore ce coût. C'est un contrat analytique fermé, PAS un banc numérique praticable annoncé ni une autorisation d'exécution. Réduire ce coût exige une nouvelle accélération avec sa propre preuve et ses propres erreurs. Les bornes sont certifiables en principe, non déjà certifiées Lean.

## 5. Annexe calculable indépendante, avec son statut exact

Pour N=100000000 entier complet, tester séparément le signal réel à t_ann=64logN/N avec K=64, h=1/32, J=4096 (8193 nœuds), tolérance globale proposée10^(-8). Ici seulement δ=π/2 et aucune extraction du coefficientN n'est revendiquée. La référence est la somme F_N(t_ann) sur TOUS les n de1 àN, avec certificats neufs de primalité, composité et de puissances premières. Elle n'utilise aucune ancienne banque, aucun masque, aucun résultat de crible arithmétique de recherche.

La queue n>N est ≤R_N, avec r_ann=e^(−t_ann),

R_N=r_ann^(N+1)[(N+1)−Nr_ann]/(1−r_ann)².

À certifier avant le calcul : R_N+C(64)+A_Mellin(t_ann,1/32)+E_J(t_ann,1/32,4096)+rayons≤10^(-8). La pleine fenêtre1..N est obligatoire, même si beaucoup de poids sont petits. Ce PASS éventuel serait HEAT_AUX_PASS, jamais COEFFICIENT_N_PASS ou D_N_PASS. Le déroulement cusp0 peut être testé comme couche indépendante sur des intégrales géométriques, avec facteur1/2, m=0 et queues de coordonnées explicites; voir numeric_contract.md. Les valeurs ζ utilisées pour évaluer φ ne deviennent pas un certificat numérique indépendant du PDE de diffusion.

## 6. Charges et ponts non payés

Écrire Q(n)=Λ(n)−(log n)1_Prime(n), non nul exactement aux puissances premières propres. Les trois contributions Q·prime, prime·Q et Q·Q dans G_N sont conservées séparément; elles ne sont pas des erreurs de troncature spectrale. Aucun passage de G_N à un nombre de représentations non pondéré n'est acquis gratuitement.

Le raccord à l'architecture bilantielle fixée doit encore relier cet observable aux coefficients physiques entiers, à la différence physique/modèle et aux termes B_prime^a, B_pp^a, P_band≥2, Z_face≥2, I_alpha et2max(e,0). Q, k=1, unités, whole U_a et toutes les frontières archivées sont gardés. Ni les contrôles scalaires majoritaires, ni l'unitarité de φ sur Re(s)=1/2, ni un déterminant ne donnent le signe ou le paiement de D_N. Le seuil source logN≥10^24 demeure distinct du test N=10^8. Aucun résultat de Hilbert–Pólya, RH, simplicité des zéros ou annulation équivalente à la cible n'est postulé.
