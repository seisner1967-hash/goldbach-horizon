# Boucle 15 — conducteur court réel et covariance du masque semipremier

**FINAL conceptuel — rôle 1.** Le rapport dérive une réduction arithmétique des images au conducteur `d=cr≤a`, puis une majoration indépendante de leur masque structurel. La norme acquiert un facteur `1/sqrt(log a)`. Ce gain est démontré par écrit, sans certification Lean nouvelle ; il ne minore aucune incidence première et Cauchy ne paie pas la covariance. Ni C16 entière ni le résidu ne sont estimés : score0, victoire fausse. Aucun Lean ou producteur ancien n'est exécuté par ce rôle.

## Quatre lignes et entrées

**Mechanism :** Réindexer toutes les images canoniques de C16 par `(d,b)=(cr,sq)`, conserver leur masque semipremier structurel entier, puis projeter ce masque sur les entiers unitaires de sa fibre ; séparer le terme AP non masqué de sa covariance réelle avec la seconde incidence première.

**Hypothesis :** Les primalités de c,r,s,q, l'ordre, les deux caps et les unités définissent le masque sans demander que `N−db` soit premier. Chebyshev est démontré ci-dessous ; aucune capacité, densité inférieure, norme favorable ou petitesse de C17 n'est postulée.

**Observable :** Conducteur arithmétique `d≤a`, multiplicité physique1, cardinal structurel majoré par `64B/log a`, norme centrée exacte, AP entière et covariance entière ; première quantité sans estimation : cette covariance signée et sa comparaison agrégée au côté parent.

**Conflicts :** Le petit conducteur de m ne donne pas les hypothèses Type I/II sur le candidat premier `n=N−m`. Les puissances propres raw, c1, les autres cofacteurs, S(cN), les restes et les frais acquis restent présents ; un PASS sur le masque ou une projection standard ne constitue pas un contournement de parité.

Entrées locales lues : PROBE15 ; retour définitif14 ; FINAL14 `agent1_coverage.md` (dont C11–C18) et `agent5.md` ; contraintes actuelles de l'arbre. Les artefacts historiques651 restent intacts. Littérature primaire consultée : Ford–Maynard, introduction, équations (I)/(II)/(w), théorème2.1 et sections4.2–4.3 ; Goldston–Graham–Pintz–Yıldırım, pages2–3, énoncé BV pour le poids premier et remarque sur sa version cumulative. Aucun résultat de détection de premiers n'est importé pour notre profil sans ses hypothèses.

## 1. Extraction fixée, et sens de la comparaison

Conserver `u=log N`, `ell=log u`, `alpha=ceil(N^(1/4))`, `Q=floor((N−1)/alpha)`, `a=ceil(N^(7/16))`, `M=ceil(N^(3/4))`, N pair. Domaine source : `u≥10^24`. Les kernels D/W gardent le Q original, leurs fronts stricts, les unités et k1 conjoint ; whole U_a comprend le bas `r≤alpha`.

Le côté parent de C16 contient les triples canoniques `(c,p,q)` avec c premier, `c≤a<p<q`, unités, bulk, et `n=N−cpq>Q` réellement premier. Le côté image contient **tous** les quadruples canoniques

```text
c,r,s,q premiers ; c<r<s≤a<q ; cr,cs≤a<rs<q ;
gcd(crsq,N)=1 ; M≤crsq≤N−Q−1 ; N−crsq premier.
```

Les images tardives sans parent descendant restent dans cette famille. Les parentés/matchings de14 ne la tronquent pas. Avec `kappa_c=log c+S(N)>0`, la comparaison principale est

```text
C16_total = sum_parents kappa_c log(N−cpq)
            − sum_images kappa_c log(N−crsq).
```

Sous U4, cette expression est le principal de l'extraction véritable, pas sa valeur physique au N fini. Les deux erreurs W sont conservées sur les supports ; leur route U4 est alternative à la variation, sans second NG54. Le S(N) affiché est celui de ce principal U4. Il ne remplace pas le S(cN) du moment bilatéral ni son terme `−S(N)N`.

## 2. Un conducteur réellement inférieur à sqrt N

Poser `d=cr` et `b=sq`. Alors `d≤a`. Pour u≥16, `a≤2N^(7/16)<sqrt N` ; le ceil est compris dans le facteur2. L'ancien conducteur `cq` pouvait aller à `N^(9/16)`. Le changement s'applique à chaque image, pas seulement à celles d'une sous-fibre favorable.

Pour des c,r premiers fixés avec `c<r`, `(cr,N)=1`, `cr≤a`, définir

```text
I_d = {b entier : ceil(M/d)≤b≤B_d},
B_d = floor((N−Q−1)/d),
U_d = {b in I_d : gcd(b,N)=1}, J_d = #U_d.
```

Le **masque structurel** `beta_{c,r}(b)` vaut1 exactement lorsqu'il existe s,q premiers tels que

```text
b=sq ; r<s ; cs≤a ; q>a ; a<rs<q ; gcd(sq,N)=1.
```

Il vaut0 sinon. L'appartenance à I_d garde bulk et `N−db>Q`. **La définition de beta n'inclut aucune primalité de N−db.** La seconde incidence est portée séparément par

```text
theta_N(n) = log n si n est réellement premier et gcd(n,N)=1 ; 0 sinon.
```

Un b admissible a un seul facteur premier `q>a`, car `s≤a/c<a`. Sa factorisation retrouve s,q ; donc beta appartient à `{0,1}` plutôt qu'à un multiensemble. Les c,r sont les deux premiers facteurs ordonnés de m ; le d semipremier retrouve c,r de manière unique. Ainsi `(c,r,b)` retrouve une image physique et chaque image est comptée une fois. Les deux caps `cr,cs≤a`, l'ordre `rs<q`, l'exclusion des carrés et les unités demeurent littéraux.

La somme image devient exactement

```text
T_images = sum_(c,r) kappa_c sum_(b in I_d)
                         beta_{c,r}(b) theta_N(N−db).
```

Il n'y a aucun masque `mu(n)^2` sur le premier axe global. Si l'on emploie raw `Lambda_N`, l'identité contient en plus la somme des puissances propres

```text
PP_beta = sum beta(b) [Lambda_N(N−db)−theta_N(N−db)].
```

Ce terme n'est jamais éliminé par la définition de beta ; son raccord utilise le poste properpowers existant une seule fois. La présente extraction demeure une sous-famille c premier, avec c1 et les autres cofacteurs hors de son support explicite.

## 3. Gain quantitatif indépendant : cardinal du masque

Voici une démonstration élémentaire, indépendante des incidences `N−db` premières. Elle ne suppose pas le résultat à obtenir.

### Chebyshev avec constante et petits x

Écrire `vartheta(x)=sum_(p≤x)log p`. Pour chaque entier j≥1, les premiers `2^(j−1)<p≤2^j` divisent le coefficient binomial `binom(2^j,2^(j−1))`. Il est au plus `2^(2^j)`, donc

```text
vartheta(2^j)−vartheta(2^(j−1)) ≤ 2^j log2.
```

Pour tout réel x≥2, choisir k avec `2^(k−1)<x≤2^k`. La somme des inégalités j1..k donne `vartheta(x)<4x log2`. Aucun résultat asymptotique ni seuil caché n'intervient. Les premiers au-dessus de sqrt x ont chacun logarithme supérieur à `(log x)/2`, et il y a au plus sqrt x premiers en dessous. Comme `log x≤sqrt x` pour x>0 (le maximum de `(log x)/sqrt x` est `2/e<1`),

```text
pi(x) ≤ sqrt x + 2 vartheta(x)/log x
      ≤ (1+8 log2) x/log x < 8x/log x,      x≥2.
```

Le cas x=2 et les petits x sont donc déjà inclus. La constante8 n'est ni une hypothèse ni une constante optimisée.

### Harmonie des facteurs s

Les gardes `r<s` et `rs>a` imposent `s²>rs>a`, donc `s>sqrt a`. La garde `cs≤a` donne `s≤a/c≤a`. Pour `log a≥8`, la sommation partielle de la majoration précédente donne

```text
sum_(sqrt a<s≤a, s premier) 1/s
 = pi(a)/a − pi(sqrt a)/sqrt a
   + integral_(sqrt a)^a pi(t)/t² dt
 ≤ 8/log a + 8 log2 < 8.
```

Tout q admissible satisfait `a<q≤B_d/s`. S'il n'existe aucun tel q, ce s donne zéro ; sinon `log(B_d/s)>log a`. On peut oublier les autres gardes pour majorer, sans les enlever du masque réel :

```text
M_beta := sum beta(b)
 ≤ sum_(sqrt a<s≤a/c, s premier) pi(B_d/s) 1_(B_d/s>a)
 ≤ (8B_d/log a) sum_(sqrt a<s≤a, s premier) 1/s
 < 64 B_d/log a.                                  (L1)
```

En particulier, au source `log a≥7u/16`,

```text
M_beta < (1024/7) B_d/u.
```

Ce gain est une **majoration de support**, pas une minoration du nombre d'images premières. Il n'implique pas une couverture du côté parent. Les nombreuses images structurelles peuvent toujours avoir un complément composite.

## 4. Projection unitaire et quantité nouvelle non estimée

Si J_d=0, beta est nul et toute la fibre vaut zéro. Sinon poser `rho_d=M_beta/J_d` et

```text
zeta_d(b)=beta(b)−rho_d 1_(b in U_d).
```

Les unités sont effectives : beta est supporté sur U_d. On obtient exactement

```text
sum zeta_d=0,
sum zeta_d² = M_beta(1−rho_d) ≤ 64 B_d/log a.        (L2)
```

Ainsi la norme possède un facteur `1/sqrt(log a)` par rapport au masque dense de longueur B_d. C'est le premier gain quantitatif indépendant de cette route.

Définir les quantités physiques de première incidence

```text
T_d = sum_(b in U_d) theta_N(N−db),
Gamma_d = sum_(b in U_d) zeta_d(b) theta_N(N−db).
```

Alors

```text
sum beta(b) theta_N(N−db) = rho_d T_d + Gamma_d.     (L3)
```

Gamma ne contient aucune cible ou capacité comme hypothèse. C'est une corrélation explicite entre la composition semipremière canonique de b et la primalité de son complément affine. La densité rho est la **densité structurelle exacte**, déterminée sans examiner la primalité du complément. Elle n'est pas une densité première prédite.

Avec `bar_theta=T_d/J_d`, le centrage donne encore

```text
Gamma_d = sum zeta_d(b) [theta_N(N−db)−bar_theta],
|Gamma_d|² ≤ M_beta(1−rho_d)
             [sum_(b in U_d)theta_N(N−db)² − T_d²/J_d]. (L4)
```

La borne triviale `theta_N≤u` et J_d≤B_d implique seulement

```text
|Gamma_d| ≤ 8u B_d/sqrt(log a).
```

Elle ne paie pas C16, même pour une fibre générale de longueur comparable à N/d. Après les poids kappa et l'agrégation, une économie de racine de logarithme ne devient pas une économie de puissance de N ou le facteur `1/(u ell)` requis. Aucun signe ni gain supplémentaire de Gamma n'est établi. L1/L2 sont un vrai gain de norme mais **ne franchissent pas la parité**.

## 5. Ce que BV contrôle après cette réduction

Le petit d donne accès seulement au morceau **non masqué** T_d. Poser

```text
b_min=ceil(M/d), b_max=B_d,
n_lo=N−db_max, n_hi=N−db_min,
X_d=n_hi−n_lo+1.
```

Soit `Psi_theta(x;d,N)` la somme de `log n` sur les n premiers `≤x`, `n≡N mod d`, sans imposer leur unité N. La reconstruction exacte est

```text
T_d = Psi_theta(n_hi;d,N) − Psi_theta(n_lo−1;d,N)
      − E_divN,d,
E_divN,d = sum_(b in I_d, n=N−db premier, gcd(n,N)>1) log n.
```

Le dernier terme comprend explicitement les premiers divisant N qui pourraient être dans l'intervalle ; il n'est pas gratuitement supprimé. Le principal AP est `X_d/phi(d)`. Remplacer X_d par `d #I_d` oublierait le front exact `(1−d)/phi(d)`.

Avec `E_theta(N,d)=max_(x≤N,(v,d)=1)|Psi_theta(x;d,v)−x/phi(d)|`,

```text
T_d = X_d/phi(d) + E_interval,d − E_divN,d,
|E_interval,d|≤2E_theta(N,d).
```

Les d=cr sont distincts et au plus a. Au source `S(N)<3ell` donne `kappa_c≤u+3ell≤2u`, et `rho_d≤1`. Par conséquent

```text
|sum_(c,r) kappa_c rho_d E_interval,d|
 ≤4u sum_(d≤a) E_theta(N,d).                        (L5)
```

L'énoncé BV primaire affiché porte sur les intervalles dyadiques `(x,2x]`, avec `E*(N,d)` leur erreur maximale. La remarque distingue la présentation cumulative usuelle ; les deux erreurs ne sont pas identifiées sans raccord. La décomposition de `(0,X]` en `(X/2^j,X/2^(j−1)]`, arrêtée lorsque `X/2^K<1`, donne explicitement

```text
E_theta(N,d) ≤ K_N E*(N,d)+1/phi(d),
K_N=ceil(log N/log2)+1.
```

La queue n'a aucun premier et son principal est inférieur à `1/phi(d)`. Donc L5, l'énoncé dyadique BV et la somme acquise `sum_(d≤N)1/phi(d)≤3(1+u)` donnent seulement, pour chaque A fixé et à un onset supplémentaire,

```text
4u sum_(d≤a)E_theta(N,d)
 ≤4u K_N C_A N/u^A +12u(1+u).
```

La condition est `a≤sqrt N/(log N)^B` ; l'exposant7/16 laisse cette marge pour tout B fixé quand N est assez grand. Le facteur K_N est conservé, quitte à augmenter A. **Constantes et onset supplémentaire ne sont pas calculés.** Aucun paiement au seul seuil `u≥10^24` ne résulte de cette forme qualitative ; ni BV(θ)>1/2 ni BV2 ne sont utilisés. [Source primaire, pages2–3, eq1.5–1.7](https://arxiv.org/pdf/math/0506067).

L5 n'est pas une application de BV à beta. Le résultat reste

```text
T_images = sum kappa_c rho_d X_d/phi(d)
           + sum kappa_c Gamma_d
           + sum kappa_c rho_d(E_interval,d−E_divN,d).
```

Le principal exact structurel, la covariance et le retrait d'unités restent séparés. La comparaison au vrai côté parent reste ouverte, même si l'erreur AP non masquée finit par être petite. Les properpowers ne sont pas cachées : theta est une extraction, et le raw entier garde PP_beta dans son raccord unique.

## 6. Lecture de Ford–Maynard et limites de raccord

Ford–Maynard considèrent deux séquences non négatives sur une tranche `(x/2,x]`. Leur différence doit vérifier des estimations Type I uniformes sur des intervalles et Type II pour tous coefficients divisoriellement bornés, ainsi qu'une croissance contrôlée ; la référence doit satisfaire une masse première inférieure et une loi factorielle générale. J'ai lu ces hypothèses aux pages1–4 et12–15. Aucun de ces énoncés n'établit nos estimations pour un profil nouveau. [Source primaire](https://www.ford126.web.illinois.edu/wwwpapers/prime-producing-sieves.pdf).

Pour raccorder notre fibre à leur variable première j, il faudrait partir de

```text
A_j = beta((N−j)/d) 1_(j≡N mod d, (N−j)/d in I_d),
B_j = rho_d 1_(j≡N mod d, (N−j)/d in U_d),
W_j = A_j−B_j,
```

puis découper le support j en tranches dyadiques, définir une normalisation et démontrer les conditions sur la référence. La petitesse `d≤a` concerne les diviseurs de **N−j**, tandis que leurs Type I/II portent sur les produits `j=v w`. Les sommes nouvelles impliqueraient donc

```text
sum W_(v w) = sum [beta((N−vw)/d)−rho_d chi_U((N−vw)/d)]
```

avec ses congruences et ses coefficients. BV sur le candidat j ne démontre pas cette corrélation semipremière décalée. L1/L2 ne la démontrent pas davantage. Aucun triplet `(gamma,theta,nu)` disponible n'est attribué à notre séquence ; aucun théorème Ford–Maynard n'est appelé comme preuve ou no-go concernant la vraie arithmétique. Le profil est explicite, l'hypothèse analytique manquante demeure explicite.

## 7. Contrat numérique15 nouveau, transmis au rôle6

**Domaine : première incidence complète d141, plus raccord physique sur un échantillon déclaré neuf.** N=100000000, alpha100, a3163, Q999999, M1000000, c3,r47,d141. Les ceil/floor donnent

```text
I_d = [7093,702127], #I_d=695035,
U_d = {b in I_d : gcd(b,10)=1}, J_d=278014.
```

Le rôle6 doit certifier ces entiers et examiner **tous** les b de I_d, sans remplacer le domaine par les seuls b dont le complément est premier. Construire beta avec les s,q réellement premiers et toutes les gardes de §2. Les s potentiels sont testés intégralement ; `rs<q`, `cs≤a`, bulk et n>Q sont gardés, pas une seule coupure en exposants. Un crible entier de la progression `N−141b` peut porter theta et raw ; primalité et puissances propres sont certifiées.

Sorties nouvelles requises :

1. Vecteurs entiers complets de beta, chi_U, primalité du complément et raw prime-powers, avec les factorisations canoniques des b à beta1 ; aucun flottant.
2. M_beta, rho rationnel, L2 exacte et L3/L4 sur les logarithmes symboliques ; somme theta complète, somme masquée et Gamma complète avec un certificat de signe strict quand non nul.
3. Contrôle L1 `M_beta log a≤64B_d` par intervalles logarithmiques stricts. À N=10^8 cette constante est large : le PASS seul ne démontre pas l'efficacité asymptotique de la norme, ni une minoration première.
4. Promotion exploratoire à falsifier **seulement si Gamma est strictement non nulle** : « le petit d autorise le remplacement exact beta→rho chi_U (Gamma=0) ». Le rejet porte sur cette promotion finie précise, pas sur BV lui-même ni sur une éventuelle estimation restreinte au source. Aucune conclusion globale n'est pré-écrite.
5. Somme raw masquée moins somme theta masquée avec tous les properpowers. Aucun `mu(n)^2` réparateur ; conserver les cas n composite hors beta et les exceptions d'unités.
6. Raccord D/W/U réel sur3–5 images physiques **nouvelles**, avec q≥4001, sélection déterministe et scope annoncé. Si un vertex est déjà stocké auparavant, le sauter dans cet échantillon de kernels uniquement ; **ne pas le supprimer du vecteur complet Gamma**. Pour ces vertices, garder U_a entier, U_alpha+annulus, Q/R stricts, unités/k1 et `C_image=−logc+W` avec les vrais coefficients. Toutes les autres erreurs W restent des termes littéraux non évalués et non payés.

Les vecteurs d'incidence complets ne sont donc pas présentés comme un calcul exhaustif de tous les kernels. Aucun ancien producteur/PASS n'est rejoué. Un succès nouveau a son unique rejeu séparé avant gel. Les résultats du rôle6 appartiendront à son reçu séparé ; ce rapport conceptuel ne fabrique aucun chiffre M_beta/Gamma ou PASS encore absent. N=10^8 demeure hors du domaine source.

## 8. Ledger, obligation de preuve et décision

Conserver le seul ledger

```text
D_N = B_prime^a + B_pp^a + P_band_ge2 + Z_face_ge2
      + I_alpha + 2 max(e,0).
```

P5 concerne K2 J2bulk **entier avant tout retrait** de principaux et erreurs. L'image extraite n'en est pas une nouvelle charge de crédit. Les images unused conservent leur masse ; les supports de variantes U4/variation ne reçoivent pas deux paiements. c1, `−S(N)N`, le modèle S(cN), cofacteurs longs, autres c de J2, J0/J1/J2 restants, H2, célibataires/faces/nonbulk, terme couvert et onset BV supplémentaire ne disparaissent pas.

Une formalisation éventuellement utile devrait dériver la **vraie définition arithmétique du masque**, la canonicalité, la multiplicité1 et le conducteur court, puis L1/L2 sous leurs gardes explicites. Un énoncé pour un masque arbitraire affirmant sa projection ou supposant Gamma petite ne répondrait pas à la tâche. Je ne propose pas de compiler uniquement cette projection standard comme percée.

Le progrès nouveau établi par écrit est la réduction réelle de conducteur des images et la majoration indépendante L1/L2 de leur norme. Le morceau AP est raccordé précisément à un résultat connu sans promotion du masque. La première quantité nouvelle sans estimation est `sum kappa_c Gamma_d` ; le côté parent et le raccord entier gardent aussi leurs obligations. **Aucune estimation indépendante suffisante de cette covariance n'est obtenue.** Aucun échec Lean n'est inventé : aucun candidat quantitatif Lean n'est soumis par ce rôle. La recherche continue, victoire fausse.
