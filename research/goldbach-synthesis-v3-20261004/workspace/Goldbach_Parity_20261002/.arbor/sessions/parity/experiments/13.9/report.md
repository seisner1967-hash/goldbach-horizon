# Boucle 17 — un mode Type II réel, son estimation et son prix local

**FINAL conceptuel du rôle 1 — production terminée.** Un caractère modulo 13 fournit un témoin quantitatif du Type II sur le vrai produit candidat `j = v w`. La référence calibrée seulement modulo 3 laisse un principal non nul. Une calibration supplémentaire modulo 13 réduit ce principal d'un facteur `1/V`, et Bombieri–Vinogradov sur **q** contrôle ce mode après un seuil supplémentaire inconnu. Le prix de la calibration sur la somme première reste explicite. Il ne s'agit ni d'une estimation de tous les coefficients Type II, ni d'une minoration agrégée de Γ, ni d'une victoire. Aucune compilation ou banque n'est exécutée par ce rôle.

## 1. Probe, sélection et énoncé de recherche

J'ai lu intégralement PROBE 17, le retour définitif 16, FINAL 1 et FINAL 5 de la boucle 16, puis une vue fraîche `constraints`. Les 799 archives restent immuables. La marge canonique A7 est acquise et n'est pas redérivée.

**Q1 — First principles : mauvaise représentation du raccord.** FINAL 16 laisse Γ_star et Type II ouverts. Dans son banc, la correction du défaut Type I de 38 à 2 garde un prix de 36 ; elle ne produit pas de Type II. Dans l'autre banc, trois incidences favorables coexistent avec un déficit entier positif. Ces deux faits interdisent de transformer une calibration ou un coefficient favorable en paiement global.

**Q2 — Hidden assumption :** une correction locale modulo 3 pourrait suffire à donner une petite somme pour tous coefficients multiplicatifs du candidat. En la supprimant, un caractère d'un autre module peut mesurer le principal résiduel sur une vraie plage de facteurs de j.

**Q3 — Elephant :** les facteurs `s q` de `N−j` ne sont pas les facteurs `v w` de j. Même un mode Type II contrôlé et son prix payé ne contrôlent ni tous les coefficients, ni les incidences parent–image de C16/C17.

**Q4 — Hamming : oui.** La première estimation choisie porte sur des facteurs candidats longs et des coefficients bornés indépendamment de la normalisation ; elle teste une obligation analytique réelle.

Les quatre mouvements sont examinés :

1. **Assumption Inversion :** tester un caractère modulo 13, plutôt que supposer que la calibration modulo 3 convient à tous les produits.
2. **Backward From Success :** écrire une paire de coefficients Type II, ses plages et son principal AP avant de chercher une minoration première.
3. **Analogical Transfer :** utiliser un mode multiplicatif comme témoin d'un biais de référence ; après correction, comparer les lois exactes `1/(v−1)` et `1/v`.
4. **Failure-Case Reverse Engineering :** conserver le prix révélé en 16, distinguer les facteurs candidats du complément et empêcher tout crédit de capacité par le nombre de représentations.

Le candidat « nouvelle norme après projection » est écarté. Le candidat « appliquer BV directement à Γ » est écarté : BV ne porte pas sur ce masque. Le survivant apporte une **estimation indépendante d'un mode Type II spécifié**, avec sa calibration payante ; l'estimation complète demeure ouverte.

Déclaration à cinq champs : hypothèse attaquée = calibration locale suffisante pour tout Type II ; mécanisme = témoin par caractère et distribution AP sur q ; chaîne causale = la loi première de q induit `1/(v−1)`, la référence entière induit `1/v`, leur différence acquiert `1/V` après calibration 13 ; orthogonalité = variables candidates, distinctes du crible de quatre formes du rôle 2 ; conflits = ni Γ petit, ni densité première, ni partenaire ne sont ajoutés.

```text
Mechanism: Témoin Type II par le caractère quadratique modulo 13 sur j=v w, réindexation AP de q modulo 13v, puis comparaison des lois 1/(v−1) et 1/v.
Hypothesis: La calibration 3 laisse un principal réel ; la calibration 39 le réduit de 1/V pour cette paire de coefficients, avec erreurs BV, unités et fronts conservés et prix L13 explicite.
Observable: Principal brut de taille x/u³, normalisé x/u, puis mode calibré 39 majoré par x/u^B à un seuil BV supplémentaire ; nouveau contrôle exact au N=10^8 sur les vrais produits candidats.
Conflicts: Un seul mode est contrôlé ; Γ39, tous coefficients Type II, parents également 13-rugueux, S(bN), rawproperpowers et ledger entier restent présents, sans victoire par projection.
```

## 2. Les poids, les produits et la normalisation

Conserver `u=log N`, `a=ceil N^(7/16)`, les α et Q originaux, et le bulk M. Choisir la sous-fibre `c=7`, `r=11`, `d=77`, avec N pair et `gcd(N,3003)=1`. Les autres N restent hors de cette extraction, sans suppression du ledger.

Cette boucle utilise la **nouvelle** fenêtre `x=N/4`, `x/2<j≤x`. Poser

```text
b_min = ceil((N−x)/77), b_max = ceil((N−x/2)/77)−1,
I = [b_min,b_max], n_lo = N−77 b_max, n_hi = N−77 b_min,
X = n_hi−n_lo+1 = 77(|I|−1)+1.
```

Le masque β(b) est celui des images canoniques : `b=s q`, s et q premiers, `11<s`, `7s≤a<11s<q`, `q>a`, unités, bulk et `j>Q`. Il ne contient pas la primalité de j. La représentation est unique. Au source, toutes les plages s sont dans `(a/11,a/7]`, q dans un intervalle comparable à `Y=N/a`, et j est comparable à N.

Définir `U_h={b∈I : gcd(b,hN)=1}`, `J_h=#U_h`, `A=Σβ`, `ρ_h=A/J_h` pour `h=3,39`. β est supporté sur U_39 au source et dans le contrat fini. Si A=0, les sommes valent zéro et aucun quotient n'est utilisé. Les profils sont

```text
z_h(j) = β((N−j)/77)−ρ_h 1_Uh((N−j)/77), h=3,39,
```

avec zéro hors de la progression et de la fenêtre. Ce sont des profils artificiels de comparaison ; aucune définition physique D/W ou S(bN) n'est remplacée.

Soit χ le caractère quadratique modulo 13 : χ=0 sur les multiples de 13, +1 sur les résidus `1,3,4,9,10,12`, −1 sur les autres unités. Poser

```text
V = ceil N^(1/8),
P = {v premier : V<v≤2V, gcd(v,3003N)=1},
ξ_v = 1_P(v) χ(v), κ_w = χ(w),
T_h = Σ_(x/2<v w≤x) ξ_v κ_w z_h(v w).
```

Les normes des coefficients sont **|ξ_v|≤1 et |κ_w|≤1**. La primalité de v définit un coefficient permis, sans prétendre que w est premier. Ici v est de taille `N^(1/8)`, w de taille `N^(7/8)`. Au source `s>2V`, `s≠13` et `q>2V`; ces gardes permettent les inversions réelles ci-dessous. La plage est contenue, à partir d'un seuil, dans un intervalle Type II ayant θ=1/8 et une largeur ν>0. On ne prétend rien pour un intervalle de facteurs qui ne contient pas cette plage.

La normalisation utilisée pour le critère Type II est la vraie masse

```text
λ=x/A, T_hat_h=λ T_h.
```

Elle multiplie les deux séquences, pas les normes de ξ et κ. Elle est liée à la densité locale par `λ=(x/J_h)/ρ_h`. La division par ρ_h seule donne une autre échelle, `J_h/A`, et conserve la proportion d'unités de N ; les deux normalisations ne sont pas confondues.

## 3. Réindexation AP : le principal est calculable

Pour s fixé, les endpoints q sont

```text
L_s = ceil(3N/(4ds))−1, H_s = ceil(7N/(8ds))−1.
```

Au source, leurs intervalles sont non vides et les autres caps sont automatiques, avec tous les arrondis conservés. On a `Y/20≤L_s≤H_s≤Y`, après le seuil source. Les s|N sont exclus réellement.

Pour v∈P, `v|j` exige `q≡N(ds)^(−1) mod v`. Pour chaque unité t modulo 13, la classe q≡t se combine par CRT avec cette classe modulo v. Les douze classes modulo 13v sont unitaires. La multiplicativité donne `ξ_v κ_(j/v)=χ(j)` et la somme locale vaut exactement

```text
Σ_(t∈(Z/13Z)^×) χ(N−ds t) = −χ(N).           (B1)
```

En effet, `t↦N−ds t` parcourt tous les résidus sauf N ; la somme du caractère sur les treize résidus vaut zéro. Les exclusions `s=v`, `s=13`, `v|77N` ne sont pas oubliées : elles sont vides ou retirées par les gardes, et ne peuvent être inversées dans une future famille élargie.

Poser

```text
h_V=Σ_(v∈P)1/(v−1), h_0=Σ_(v∈P)1/v.
```

La masse q dans une classe modulo 13v a principal `C_s/[12(v−1)]`, où C_s est le **vrai nombre entier de q premiers** de l'intervalle avant exclusion q|N. On peut choisir cette masse réelle comme référence AP en soustrayant aussi son erreur ordinaire ; on ne remplace donc pas A par un Li approximatif dans le principal final.

Cette réindexation donne

```text
Σ ξ_v κ_w β((N−v w)/77) = −χ(N) A h_V/12 + R_AP + R_unit,
|R_unit|≤4a.                                  (B2)
```

Pour justifier le dernier frais : q>a divisant N sont au plus 3 ; il y a au plus a/7 valeurs s. Chaque candidat j≤N a au plus 8 facteurs premiers distincts dans P, car `v>N^(1/8)`. La suppression des paires non unitaires coûte au plus `24a/7`; la différence entre leur masse entière et le principal `A h_V/12` coûte moins que le reliquat, puisque h_V≤2. Les représentations v divisant j appartiennent à la somme analytique ; elles ne deviennent pas des capacités physiques supplémentaires.

### Erreur AP et seuil supplémentaire

La source primaire utilisée est le BV dyadique pour θ, équations (1.5)–(1.7), avec maximum sur classes unitaires et endpoints. [Goldston–Graham–Pintz–Yıldırım](https://arxiv.org/pdf/math/0506067). La reconstruction cumulative conserve

```text
E_θ(Y,k) ≤ K_Y E*_θ(Y,k)+1/φ(k),
K_Y=ceil(log Y/log 2)+1.
```

Sur `[L_s,H_s]`, la sommation partielle convertit le maximum cumulatif θ en une erreur de compte π au plus `3 E_θ(Y,k)/log(Y/20)`. Pour remplacer Li par le vrai C_s, elle ajoute l'erreur ordinaire k=1, pondérée par 1/φ(k). Toutes les classes et tous les s sont donc majorés, sans « BV sur β » :

```text
|R_AP|≤R_BV,
R_BV= [42a/(7 log(Y/20))]
       [K_Y C_F Y/(log Y)^F + 3(1+u)].          (B3)
```

Le dernier terme utilise la borne acquise sur la somme des inverses de φ jusqu'à N, plutôt qu'un nouveau seuil pour Y. Le BV est appelé seulement si `26V≤sqrt(Y)/(log Y)^G`, G dépendant de F. La marge en exposants est `9/32−1/8=5/32`; elle assure cette garde **éventuellement**, sans calculer C_F ni le seuil. B3 est `O_F(N/u^F)+O(a)`, à un onset BV supplémentaire inconnu. Rien n'affirme que cet onset est payé au seul u≥10^24, ni au N=10^8.

## 4. Ce mode Type II après calibration 39

La référence de U_3 a une moyenne χ nulle. Sur chaque progression b imposée par v et un diviseur de 3N, un bloc de treize termes annule le caractère. L'inclusion-exclusion et `2^ω(N)≤2sqrt(N)` donnent

```text
|Σ ξ_v κ_w ρ_3 1_U3|≤52 ρ_3 V sqrt(N).        (B4)
```

La référence U_39 exclut b≡0 modulo 13. Sur ses douze classes, la moyenne du caractère de j est `−χ(N)/12`. Pour chaque v∈P, son compte de divisibilité a principal `J_39/v`, avec le front exact en erreur. Un comptage des blocs de treize et inclusion-exclusion fournit le majorant conservateur

```text
Σ ξ_v κ_w ρ_39 1_U39 = −χ(N) A h_0/12 + R_front,
|R_front|≤120 ρ_39 V sqrt(N).                 (B5)
```

Les constantes de B4/B5 sont élémentaires. Un bloc incomplet de χ coûte au plus 13. Pour B5, utiliser le profil `1_(b unit13)[χ(N−77b)+χ(N)/12]` : sa somme par bloc de treize est nulle et un bloc incomplet coûte au plus 26. Le masque 13 est déjà dans ce profil ; l'inclusion-exclusion porte donc sur **rad(3N)**, avec au plus `2·2^ω(N)≤4sqrt(N)` termes, soit un coût de 104sqrt(N). Le compte de U_39 dans la progression imposée par v diffère de `J_39/v` d'au plus `16sqrt(N)` ; son coefficient 1/12 ajoute moins de 2sqrt(N). Le majorant 120sqrt(N) par v garde donc une marge.

B2–B5 donnent les deux **vrais** bilinéaires :

```text
T_3  = −χ(N) A h_V/12 + E_3,
|E_3|≤R_BV+4a+52ρ_3 V sqrt(N),
T_39 = −χ(N) A(h_V−h_0)/12 + E_39,
|E_39|≤R_BV+4a+120ρ_39 V sqrt(N).              (B6)
```

Le gain n'est pas une norme de projection : c'est la différence de **deux lois de divisibilité réellement dérivées**,

```text
0≤h_V−h_0=Σ_(v∈P)1/[v(v−1)]≤h_V/V≤2/V.      (B7)
```

La minoration structurelle de 16 s'adapte à cette nouvelle fenêtre : l'intervalle q a longueur au moins `N/(8ds)−2`, plus grande que le coût utilisé dans son argument AP. Ainsi A≥`N/(400d u²)` au source. Les mêmes bornes π_AP3, à leurs deux endpoints≥8·10^9, montrent `h_V≥1/(2u)` : les v|N retirent au plus 8 premiers de cette plage. Aucun candidat j premier n'est minoré par ces faits. [Bennett–Martin–O'Bryant–Rechnitzer, théorème 1.3](https://arxiv.org/pdf/1802.00085).

Pour h=3 ou 39, le comptage CRT donne au source

```text
J_h ≥ N/[32d(1+u/log 2)].
```

Il utilise `N/φ(N)≤ω(N)+1≤1+u/log2`, obtenu en ordonnant les premiers divisant N, et les erreurs de front `2^ω(hN)`. Après la normalisation exacte, B6/B7 deviennent

```text
|T_hat_39| ≤ x/(6V) + (x/A)(R_BV+4a)
             +120x V sqrt(N)/J_39.            (B8)
```

Pour tout B fixé, choisir F>B+3 dans B3 donne **ce mode** `|T_hat_39|≤x/u^B` à un seuil supplémentaire dépendant de BV. Le premier et le dernier frais ont une économie de puissance de N. Ce résultat ne concerne pas tous les ξ,κ, et n'établit pas le Type II complet requis par un crible produisant des premiers.

### Ordres et obstruction de la référence 3

Cette fibre fixe a une plage s de rapport constant 11/7, donc `Σ_s1/s` est de taille 1/u. La primalité de q ajoute un autre facteur 1/u : `A` et `A_struct=Σ_s(Li(H_s)−Li(L_s))` sont de taille `x/u²`, et non x/u. Le principal brut de T_3 est donc de taille **x/u³**. Pour T_hat_3, il est de taille **x/u**. B3 donne éventuellement `|T_hat_3|≥x/(100u)` et le signe `−χ(N)` ; ce seuil supplémentaire demeure inconnu.

La référence 3 échoue ainsi à une borne Type II sur cette plage lorsque B>3 à l'échelle brute, ou B>1 à l'échelle normalisée. La condition (II) quantifie bien sur des coefficients bornés, avec leur produit candidat ; elle n'est pas déduite de `d s q`. [Ford–Maynard, équation (II)](https://www.ford126.web.illinois.edu/wwwpapers/prime-producing-sieves.pdf). Ce diagnostic ne concerne pas une autre référence, une autre plage ou un hypothétique estimateur de Γ agrégé.

## 5. Le prix L13 et les obligations restantes

Avec θ_N(j) pour les vrais premiers unitaires, poser `Tθ_h=Σ_Uh θ_N(N−77b)` et `Γ_h=Σ z_h(j) θ_N(j)`. Les relations sont exactes :

```text
Γ uniforme = Γ_3 + L3,
Γ_3 = Γ_39 + L13,
L13 = ρ_39 Tθ_39 − ρ_3 Tθ_3.                  (B9)
```

L3 reste son prix acquis ; aucune nouvelle calibration ne l'efface. Pour L13, le masque retire b≡0 modulo 13, tandis que la primalité du candidat exclut b≡N·77^(−1) modulo 13 : ce sont **deux classes différentes**. Si les classes unitaires sont équilibrées, `ρ_39=(13/12)ρ_3`, et les principaux AP de Tθ_3 et Tθ_39 comptent respectivement douze et onze classes au module 3003. Le rapport est `143/144`; le prix principal L13 vaut **−1/144 du principal 3**. Sans équilibre exact, garder J_3,J_39, X, toutes les erreurs AP et les exceptions p|N dans B9.

Le témoin bilinéaire a son **propre** prix, avec ses propres poids :

```text
L13_II = Σ_(v,w) ξ_v κ_w [ρ_39 1_U39−ρ_3 1_U3]((N−vw)/77),
T_3 = T_39 + L13_II.                          (B10)
```

B10 ne confond pas L13_II avec le prix premier L13 de B9. On peut vérifier B10 avec un poids supplémentaire raw Λ_N(vw), en le gardant sur les trois sommes. Les candidats premiers ne contribuent pas à ce produit puisque j>v ; les properpowers peuvent contribuer et ne sont pas supprimées.

Les parents p,q de C16 sont aussi 13-rugueux dans cette branche ; ce prix ne devient pas un crédit positif gratuit contre les parents. S(bN) au vrai cofacteur et la référence−S(N)N restent acquis. Le témoin B6 porte sur les candidats composés `v w` ; chaque candidat premier >2V n'a aucun facteur v dans P. Il fournit une information de crible, pas directement une minoration des incidences premières de Γ_39.

Restent ouverts : les autres coefficients Type II, les calibrations locales et leurs prix, l'agrégation pondérée en d, Γ_39, la comparaison parent–image entière et le complément du ledger. Aucun Γ petit, aucune densité première et aucune disponibilité ne sont postulés. La formalisation de B1 seule serait une identité auxiliaire ; elle n'est pas proposée comme victoire.

## 6. Contrat numérique neuf, à sélectionner avant exécution

N=100000000, x=25000000, V=10, c=7, r=11, d=77, a=3163, Q=999999, M=1000000. La nouvelle fenêtre complète est

```text
12500000<j≤25000000,
974026≤b≤1136363, |I|=162338.
n_lo=12500049, n_hi=24999998, X=12499950,
X−77|I|=−76 ; φ(77)=60, φ(231)=120, φ(3003)=1440.
```

Les fronts et tous les comptes sont à vérifier. Les propres bornes de complétude sont `293≤s≤451`, `q≤floor(1136363/293)=3878`; les premières bases jusqu'à5000 couvrent les candidats j≤25000000. P est construit exactement : les premiers de `(10,20]` sont examinés, les v|3003N sont retirés ; v=17,19 restent. Chaque quotient w=j/v est réellement entier. β n'est pas filtré par la primalité de j.

**Les caps ne sont pas automatiques au fini.** Pour les comptes AP qui reconstruisent β, utiliser les endpoints réellement coupés

```text
L_s^phys = max(a,11s,11,ceil(b_min/s)−1),
H_s^phys = floor(b_max/s),
q premier avec L_s^phys<q≤H_s^phys.
```

Un intervalle vide donne zéro. Les endpoints non coupés `ceil(3N/(4ds))−1` et `ceil(7N/(8ds))−1` de la dérivation source peuvent être enregistrés séparément pour expliquer la coupure, mais ils ne définissent pas les C_s physiques au N=10^8. B2 est vérifiée au fini avec les C_s et résidus exacts de ces **vrais** endpoints physiques. Ici la classe exclue par 13|j est b≡4 modulo 13, distincte de b≡0 retirée par U_39.

Sorties nécessaires :

1. Tous les b de cette fenêtre, les masques U_3/U_39 et β, leurs vrais facteurs et caps ; A,J_h,ρ_h, fronts X et les classes modulo 3 et 13. Les recettes compactes complètes sont admises, sans duplications de gros kernels.
2. Tous les vrais couples `v,w` avec v∈P et j=v w dans la fenêtre/progression ; multiplicité par j déclarée. Vérifier `χ(v)χ(w)=χ(j)`, les normes≤1, les sommes rationnelles T_3,T_39 et leur prix L13_II, l'identité B10, ainsi que leur normalisation x/A si A>0.
3. Les comptes AP q dans les douze classes unitaires de 13v, avec les endpoints physiques L_s^phys/H_s^phys et les retraits q|N ; toute comparaison aux endpoints source est séparée. Vérifier B1 et la décomposition B2/B6 avec **résidus finis exacts**, h_V/h_0, références et fronts. Ne pas appliquer BV ou écrire son signe asymptotique à N=10^8.
4. Toutes les incidences candidates θ et rawproperpowers unitaires de la progression. Les primes candidats ne contribuent pas au témoin Type II car j>v ; les properpowers restent séparées, y compris celles divisibles par 13. Vérifier aussi B10 avec le poids raw. Vérifier Γ_3−Γ_39=L13 sur les logarithmes encadrés strictement, avec son prix premier distinct de L13_II ; aucun signe pré-écrit ni monotonie supposée de calibration.
5. Garder les erreurs D/W du raccord physique littéralement non évaluées. Aucun kernel ancien ou nouveau n'est nécessaire à cette question Type II ; aucune banque ancienne n'est rejouée. Le producteur nouveau et son unique copie isolée respectent la conservation 799.

Ce banc vérifie une dérivation et mesure un mode ; il ne prouve ni le seuil BV, ni la suffisance de ce mode pour Γ, ni une disponibilité globale. Les erreurs numériques réelles sont archivées avant réparation s'il y en a ; aucune falsification n'est présupposée.

## 7. Décision et ledger

La proposition retenue est B6–B8 : **une estimation quantitative d'un mode Type II réel après calibration payante**, avec un défaut principal explicite avant cette calibration. Son caractère limité est partie de l'énoncé, pas une exception cachée.

Le ledger demeure `D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0)`. P5/K2 porte sur J2 bulk entier avant retraits ; U4 et variation restent alternatives, sans second NG54. α/Q originaux, whole U_a, raw sans μ(n)^2, c1/e1/b1, S(bN), cofacteurs longs, référence−S(N)N, faces et restes restent présents. A7 est acquis mais ne donne pas de disponibilité. Le source u≥10^24 reste distinct du banc N=10^8 et de l'onset BV supplémentaire.

**Résultat : partiel, score 0, victoire fausse.** Aucun certificat Lean pertinent de contournement complet n'est soumis. La recherche continue sur les autres modes et la comparaison agrégée.
