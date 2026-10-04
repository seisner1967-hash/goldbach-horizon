# Boucle16 — dérive Type I réelle et correction locale du conducteur77

**FINAL conceptuel, rôle1 — production TERMINÉE.** Une référence uniforme sur les unités ne partage pas, même au premier niveau Type I, la distribution locale du masque semipremier. Pour la fibre fixe c7/r11, une dérivation indépendante à partir des premiers q donne au source un défaut normalisé au moins x/8 pour le diviseur3 du **candidat** j. La correction sur b unitaire modulo3 retire ce principal et isole une covariance résiduelle. Cette dernière et la comparaison entière aux parents restent sans estimation. Aucun contournement, aucun candidat Lean quantitatif et aucune victoire ne sont obtenus. Les preuves de ce rapport sont écrites ; elles ne sont pas certifiées par Lean.

## Observation, protocole et quatre lignes

Entrées lues intégralement : PROBE16, retour FINAL15, FINAL1_15, FINAL5_15 et vue fraîche `constraints` de l'arbre. Toutes les anciennes701 productions sont conservées. Aucun ancien test, gate, Lean ou rendu n'est exécuté. Les références extérieures citées ci-dessous sont lues dans leur source primaire aux passages utilisés.

**PROBE BLOCK**

- **Q1 First principles : wrong representation / wrong credit assignment.** FINAL1_15 §6 laisse les conditions Type I/II non démontrées ; FINAL5_15 confirme que la petite taille de d ne paie pas Γ. Le banc d141 donne Γ strictement négative malgré un centrage structurel exact ; le supplément L4 ne donne qu'un gap Cauchy positif. Ces deux observations demandent de tester la référence, avant de chercher une meilleure norme.
- **Q2 Hidden assumption :** une densité uniforme sur les unités de N pourrait être une bonne référence Type I du candidat j. En la supprimant, on peut extraire le biais entre les classes b=0 et b=N/d modulo un petit premier, sans imposer la primalité de j dans β.
- **Q3 Elephant :** même une référence locale corrigée n'estime pas les produits j=vw pondérés avec v,w longs. La compensation entre les deux vrais côtés de C16, les erreurs W et tout le complément du ledger demeure nécessaire.
- **Q4 Hamming : oui.** Vérifier la référence sur un vrai diviseur du candidat est une obligation mathématique préalable à toute application de Type I/II ; sa dérive de taille principale localise une erreur de raccord plutôt qu'un réglage de constante.

Les **quatre mouvements** sont exécutés avant sélection :

1. **Assumption Inversion :** conserver β réel et remplacer seulement sa référence artificielle par une référence ayant la même exclusion locale modulo3. La différence à la référence15 est gardée comme terme exact.
2. **Backward From Success :** un estimateur utilisable de Γ devrait commencer par un poids de différence satisfaisant Type I sur j. Tester v3 et écrire la somme de q dans sa vraie AP fournit ce signal manquant ; Type II ne vient pas de cette étape.
3. **Analogical Transfer :** appliquer l'idée de résidu calibré, avec une contrainte marginale arithmétique connue, à un profil de crible. La calibration est limitée à une classe locale ; elle n'est pas un modèle premier indépendant acquis.
4. **Failure-Case Reverse Engineering :** le remplacement exact β→ρ de15 est faux ; la confusion produits de N−j / produits de j est interdite ; la duplication de capacités de14/15 est fausse. La première correction requiert un drift réel v|j, la seconde une réindexation q dans une AP, la troisième le maintien de tous vertices et des modèles acquis.

**Sélection et auto-filtrage.** Le candidat « norme plus petite après projection CRT » est éliminé comme gain de norme seul. Le candidat « appliquer Chen/P3 ou un résultat général Type I/II à β » est éliminé : ni les plages ni la comparaison complète ne sont vérifiées. Le survivant est un **diagnostic quantitatif de référence Type I**, avec correction locale et question finie neuve ; il ne sert pas de certificat de victoire.

Déclaration à cinq champs du survivant : hypothèse attaquée = centrage uniforme suffisant ; mécanisme = calibration arithmétique d'une référence ; chaîne = la réindexation en q prédit une masse locale non nulle car q reste premier dans une classe non nulle, vérifiée par le vrai compte v|j ; orthogonalité = agit sur la distribution candidate, distincte de la fusion OR du rôle2 ; conflits = la covariance15 est conservée, sa promotion exacte déjà réfutée n'est pas réintroduite.

```text
Mechanism: Calibration locale du vrai poids candidat par la divisibilité de j=N−77sq par3, avec AP effective sur q et correction de référence conservée.
Hypothesis: Pour c7/r11 et3∤77N, le masque exclut b0mod3 alors que j3divisible sélectionne une classe non nulle ; son drift TypeI se dérive des qpremiers, sans petitesseΓ ni capacité supposée.
Observable: Drift normalisé uniforme≥x/8 au source, drift corrigé avec erreur locale explicite, puis test neuf complet d77/xN5 des deux références et de leur différenceΓ.
Conflicts: Le défaut concerne cette référence artificielle ; Γrésiduel/TypeII/C16, modèles S(bN), rawproperpowers et ledger entier restent ouverts, aucune projection standard n'est un Win.
```

## 1. Profil réel, fenêtre candidate et poids

Conserver u=logN, ell=logu, α=ceilN^(1/4), Q=floor((N−1)/α), a=ceilN^(7/16), M=ceilN^(3/4). Le domaine analytique est u≥10^24. N est pair. Pour cette sous-fibre seulement, imposer **gcd(231,N)=1**, c=7, r=11, d=77. Les branches N divisible par3/7/11 restent dans le complément initial ; elles ne sont pas supprimées du bilan global.

Poser x=N/5 et sélectionner le **candidat j** dans `(x/2,x]`. Définir les entiers

```text
A_b=ceil((N−x)/d), B_b=ceil((N−x/2)/d)−1,
I={b entier:A_b≤b≤B_b}, U={b∈I:gcd(b,N)=1}, J=#U.
```

Cette convention reste valable lorsque N/5 n'est pas entier. Les n_lo=N−dB_b et n_hi=N−dA_b sont les vrais fronts du candidat. β(b)=1 exactement si b=sq avec s,q premiers, r<s, cs≤a<rs<q, q>a et gcd(sq,N)=1. Aucune primalité de j n'entre dans β. Les caps imposent `a/11<s≤a/7`; chaque b a un q>a et un s<a, donc un seul représentant. Poser A=Σβ et ρ=A/J quand J>0. Les profils sur **les produits candidats** sont

```text
a_j=β((N−j)/77), b_j=ρ1_U((N−j)/77), w_j=a_j−b_j,
```

avec zéro hors des j≡N mod77 de cette fenêtre. Ici b_j est une **référence artificielle de comparaison** ; elle ne remplace pas le modèle bilatéral S(bN), le principal acquis S(N), ni le bracket physique D/W.

Au source, cette fenêtre est bulk et j>Q. Pour tous s∈(a/11,a/7], ses q satisfaisant la fenêtre sont au-dessus de a et rs : leurs tailles sont au moins une constante explicite fois N/a, et `(N/a)/a≥N^(1/8)/4`. Les ceil ajoutent seulement les corrections décrites ci-dessous. Ainsi la plage est réellement s≈N^(7/16), q≈N^(9/16), j≈N ; d reste77. La factorisation b=sq ne constitue toujours pas une factorisation j=vw.

## 2. La vraie somme Type I sur q

Pour un premier v et un s fixé, `v|j=N−dsq` devient `dsq≡N modv`. Les cas suivants sont distincts :

- si v|d ou v|N, sous les unités physiques correspondantes la contribution est nulle ; aucune inversion non unitaire n'est faite ;
- si v|s et v∤dN, j≡N modv, donc aucun candidat divisible parv dans cette branche ;
- si v∤dsN, le q est dans la classe **non nulle** `N(ds)^(−1) modv` ;
- les branches q=v, s=v et candidat j=v restent des exceptions littérales si elles sont dans une future plage. Dans notre route v3 au source, s,q,j>3, elles sont vides par les gardes.

Pour v3 et gcd(231,N)=1, tous s admissibles et q sont unitaires modulo3. Si f=N d^(−1) mod3, alors `3|j` signifie b≡f, avec f∈{1,2}. Chaque s donne un q dans l'une des deux classes unitaires de3, selon sa vraie inverse. Écrire J_t=#(U∩{b≡t mod3}) et A_t=Σ_(b≡t)β. On a A_0=0, A=A_1+A_2 et exactement

```text
Σ_(3|j) w_j = A_f−ρJ_f.                       (T1)
```

Ce sont les divisibilités du candidat j, et non les facteurs de N−j, qui sont testées.

## 3. Une borne indépendante et effective pour T1 au source

Le seul théorème extérieur utilisé ici est l'énoncé π en AP de **Bennett–Martin–O'Bryant–Rechnitzer, Theorem1.3**, pages4–5 : pour le module3, chaque classe unitaire a erreur au plus `x/[840(logx)^2]` autour de Li(x)/2 lorsque x≥8·10^9. Aucune GRH ni nouveau seuil Siegel n'est ajouté. Le même article donne le seuil et les constantes pour θ utilisés en§5. [Source primaire](https://arxiv.org/pdf/1802.00085).

Les endpoints q pour s fixé sont

```text
L_s=ceil(4N/(5ds))−1,
H_s=ceil(9N/(10ds))−1,
C_s(t)=π(H_s;3,t)−π(L_s;3,t).
```

Le dernier endpoint correspond au strict j>N/10 ; avec N/10 entier il est `floor((9N/10−1)/(ds))`. Les endpoints satisfont L_s,H_s≥a≥8·10^9 au source. Les erreurs sont donc conservées **aux deux endpoints**, même si l'intervalle est court. La différence à la moitié du nombre entier de q premiers est au plus

```text
|C_s(t)−(C_s(1)+C_s(2))/2|
 ≤ (H_s+L_s)/(840(loga)^2)
 ≤ N/(420ds(loga)^2).
```

Pour L=loga, la majoration Chebyshev acquise de15 et la sommation partielle donnent, pour L≥2log11,

```text
Σ_(a/11<s≤a/7, sprime)1/s
 ≤ 8/(L−log7)+8log((L−log7)/(L−log11))
 <12/(L−log11) ≤24/L.
```

Les s divisant N sont exclus réellement. Il y a au plus u/log(a/11)<3 au source. Les q>a divisant N sont au plus u/L<3 ; leur suppression peut modifier la différence A_f−A/2 d'au plus3/2 par s. Puisque le nombre entier de s possibles est au plus a/7, cette dernière correction est inférieure à a. On obtient, sans distribution du candidat premier supposée,

```text
|A_f−A/2| ≤ E3,
E3=2N/(35dL^3)+a.                             (T2)
```

Une minoration **structurelle** indépendante de A s'obtient dans la sous-plage `[a/10,a/8]`. La somme des deux énoncés π_AP3 implique au source au moins `a/(80L)` premiers s dans cet intervalle. En retirant les s|N, il reste au moins `a/(160L)`. Pour chaque tel s, les endpoints q ont H_s−L_s≥N/(10ds)−2 et logH_s≤u. Les mêmes deux erreurs AP, puis les au plus3 q|N, donnent

```text
#q admissibles ≥ N/(20dsu),
A ≥ [a/(160L)]·[8N/(20dau)]
  = N/(400duL) ≥ N/(400du²).                   (T3)
```

Voici les gardes des minorations utilisées, pour rendre les petits frais contrôlables : L≥24, a/10≥8·10^9 ; l'erreur de comptage s est au plus `3a/[5600(L−log10)^2]`, inférieure à a/(80L) ; les frais q demandent

```text
(1/20−u/(210L²))·N/(dsu) ≥ 2/u+3.
```

Tous ces points découlent du source u≥10^24, L≥7u/16, a≤2N^(7/16), ds≤77a/8 et de l'accroissement exponentiel de N/a. Aucun de ces seuils n'est prétendu satisfait au banc N=10^8. T3 ne minore aucun candidat j premier : seulement le masque β.

Le comptage exact des unités par inclusion-exclusion sur radN, avec 3∤N, donne

```text
|J_t−J/3|≤(4/3)·2^ω(N)≤4√N.
```

La dernière majoration utilise 2^ω(N)≤τ(N)≤2√N. Comme ρ≤1, T1–T3 donnent

```text
A_f−ρJ_f ≥ A/6−E3−4√N.                       (T4)
```

Les rapports aux frais vérifiables sont

```text
[2N/(35dL³)]/A ≤800u²/(35L³) ≤273/u,
a/A ≤400da u²/N ≤800d u² exp(−9u/16),
4√N/A ≤1600d u² exp(−u/2).
```

Chacun des deux derniers rapports est inférieur à1/100, et 273/u<1/100, au source. En particulier T4 est au moins **A/8** (les trois frais ensemble sont moins que3A/100, inférieur à A/24). Normaliser les deux profils par x/A donne

```text
Σ_(3|j) (x/A)w_j ≥ x/8.                        (T5)
```

L'expression Type I de Ford–Maynard comporte en particulier cette somme pour v3, avec coefficient positif τ(3)^B et un maximum sur intervalles. Sa borne x/(logx)^B ne peut donc valoir, pour aucun B fixé positif à N suffisamment grand, pour **cette référence uniforme normalisée**. L'énoncé(I), pages1–2, est la seule partie du résultat utilisée pour cette implication. [Source primaire](https://www.ford126.web.illinois.edu/wwwpapers/prime-producing-sieves.pdf).

T5 n'est pas un no-go arithmétique pour Goldbach, pour une autre référence ou pour le poids complet du ledger. Il n'impute pas au compilateur une erreur qui n'a pas eu lieu. C'est un défaut de raccord Type I identifié et minoré pour ce profil artificiel.

## 4. Correction locale et vraie différence au centrage15

Définir J*=J_1+J_2 et ρ*=A/J*, puis

```text
b*_j=ρ*1_(b∈U, bunit3), w*_j=β(b)−b*_j.
```

A>0 implique J*>0 et β≤1_(bunit3), donc ρ*≤1. La référence corrigée a exactement la même masse entière A. Elle garde ses fronts et toutes les unités N. Son défaut v3 est exactement A_f−ρ*J_f. Le même calcul et les déséquilibres de classes par inclusion-exclusion donnent

```text
|Σ_(3|j)w*_j|≤E3+8√N.                         (T6)
```

Cette seule marge locale gagne une puissance de u après normalisation, avec les constantes et frais précédents. **Ce n'est pas la condition Type I entière**, ni une estimation Type II : les autres v, les coefficients divisoriels et les plages j=vw restent à traiter. Aucun triplet (γ,θ,ν) n'est affecté à notre séquence.

Avec θ_N(j)=logj pour j premier unitaire et zéro sinon, poser T_t=Σ_(U,b≡t)θ_N(N−db). Puisque j>Q>3 et f≠0, T_f=0. Appeler g l'autre classe non nulle et

```text
Γ*=Σ_(b∈U)w*_j θ_N(j),
L3=ρ*T_g−ρ(T_0+T_g).
```

Alors la covariance15 de cette sous-fibre reste exactement

```text
Γ=Γ*+L3.                                      (T7)
```

La différence L3 n'est pas absorbée dans Γ* ni supprimée. Si l'on affiche la norme corrigée `A(1−A/J*)`, elle ne paie pas Γ*. La dérivation choisie est T1–T6 quantitative ; elle n'est pas une autre projection présentée comme une percée.

## 5. Principal local AP du candidat et sa direction

Poser X=n_hi−n_lo+1, avec les fronts exacts du§1. Pour t0 et tg, le candidat est dans une classe unitaire v_t=N−dt modulo3d=231. Ainsi

```text
T_t=θ(n_hi;231,v_t)−θ(n_lo−1;231,v_t)−E_divN,t
   =X/φ(231)+E_t−E_divN,t,
L3=(ρ*−2ρ)X/φ(231)
    +(ρ*−ρ)(E_g−E_divN,g)−ρ(E_0−E_divN,0).    (T8)
```

Le retrait E_divN,t des premiers divisant N est conservé. Au source, un tel premier dans cette fenêtre a au moins N/10, donc leur nombre est au plus u/log(N/10)<2 et leur masse au plus2u. Les bornes θ_AP du même Theorem1.2, applicables au module231 avec endpoints≥8·10^9, majorent les deux erreurs par `(n_hi+n_lo−1)/[840log(n_lo−1)]` par classe. Elles ne sont appliquées ni à β ni à Γ*.

Quand les trois comptes J_t sont égaux, ρ*=3ρ/2 et le principal T8 est **−ρX/[2φ(231)]**, exactement −1/4 du principal uniforme ρX/φ(77). Si les comptes sont inégaux, le coefficient littéral `(A/J*−2A/J)` est gardé ; les erreurs de comptage et AP restent dans T8. La direction principale diminue l'incidence image par rapport au modèle uniforme. Elle n'apporte donc pas un crédit favorable gratuit à C16.

Les vrais parents de C16 ont aussi leurs grands facteurs p,q unitaires modulo3 dans cette branche. Un modèle local pour leur axe a le même besoin de correction ; aucun gain parent–image ne découle du seul facteur3/4. Aucune somme sur d n'est retirée de K2 avant application de P5 entier. L'autre modèle S(cN), la référence−S(N)N et les kernels physiques restent à leur place.

## 6. Type II encore manquant

Pour cette référence corrigée, une vraie somme Type II prendrait la forme

```text
Σ_(x/2<vw≤x) ξ_v κ_w [β((N−vw)/77)
 −ρ*1_((N−vw)/77∈U, gcd((N−vw)/77,3)=1)],
```

avec la congruence vw≡N mod77, les gardes entières et une plage explicite de v. Aucun estimateur uniforme pour tous ξ,κ divisoriellement bornés n'est démontré. Les variables s≈N^(7/16), q≈N^(9/16) factorisent le complément, pas v,w. Ni BV ordinaire ni T6 ne fournissent ce dernier énoncé. L'agrégat pondéré Σ_(c,r)κ_cΓ_d et le côté parent de C16/C17 ne sont donc toujours pas estimés.

La lecture exploratoire de Matomäki–Zuniga-Alterman sur les cribles pondérés avec switching est limitée à l'abstract et l'introduction : son existence de prime avec presque-premier à au plus trois facteurs ne prouve ni notre support exact de quatre facteurs, ni la comparaison signée entre deux familles canoniques. Aucun résultat n'en est importé. [Source primaire](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/weighted-sieves-with-switching/986429394BA969687D48224E177E2F1C).

## 7. Contrat fini neuf soumis au root pour sélection

N=100000000, α100, Q999999, a3163, M1000000 ; c7/r11/d77 ; x=20000000. La fenêtre candidate est complète `(10000000,20000000]` dans sa progression :

```text
I_b=[1038962,1168831], #I=129870,
J=51948, J0=J1=J2=17316, f=2, g=1,
n_lo=10000013, n_hi=19999926, X=9999914,
X−77#I=−76 ; φ77=60 ; φ231=120.
```

Tous ces entiers sont à vérifier indépendamment par le rôle6. Le nombre entier d'unités vaut les comptes affichés parce que #I est un multiple de30 et U est l'unité modulo10. Le test ne suppose ni signe du drift ni présence d'images premières.

Les propres bornes de complétude sont : rs>a implique s≥288 et le premier s possible est293 ; cs≤a impose s≤451 ; q≤floor(1168831/293)=3989. Une liste entière exhaustive de premiers jusqu'à3989 suffit aux deux facteurs s,q. Les diviseurs/bases pour la progression candidate jusqu'à20000000 doivent être couverts jusqu'àisqrt(20000000)=4472. La suffisance historique d141 n'est pas transportée.

Sorties nécessaires, **uniquement après sélection root** :

1. Tous les b de I, les comptes des trois classes/unités et tous les β avec leurs facteurs premiers canoniques, fronts, bulk, unités et q/r/s caps ; aucune filtre j premier dans β.
2. A, A0/1/2, ρ et ρ*, les vrais comptes v3|j et T1/T6 exacts. Falsifier « la référence uniforme est exactement centrée pour TypeI3 » seulement si le vrai drift est non nul ; n'importe quel signe est admissible.
3. Tous les vrais premiers candidats et rawproperpowers unitaires de la progression, répartis par classes. Certifier T_f=0 pour θ et **garder les properpowers de raw dans cette classe s'il y en a**. L'identitéΓ=Γ*+L3 est vérifiée sur logarithmes rationnellement encadrés.
4. Les fronts X−77#I et les principaux AP de231, avec coefficients exacts J,J*, sans signe de L3 présupposé et sans invocation de la borne source à ce N hors source.
5. Les kernels D/W ne sont pas nécessaires à cette question de référence ; leurs erreurs et leur raccord au ledger restent des obligations littérales. Aucun ancien gate n'est rejoué. Une seule copie isolée du nouveau test après PASS est autorisée selon le protocole, avec conservation701 avant/après.

Ce test est une falsification possible du raccord uniforme et une mesure de la correction locale. Il ne certifie pas T5 au source, TypeII, une disponibilité de parents ou le résidu.

## 8. Ledger et décision

Le seul ledger reste D_N=B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0). Q et α originaux, U_a entier y compris≤α, rawΛ_N sans μ(n)^2, c1/e1/b1, S(bN) au vrai cofacteur supprimé,−S(N)N, cofacteurs longs, J0/J1/J2 restants, célibataires/faces/nonbulk, terme couvert et onset BV supplémentaire restent présents. Les frais U4/variation sont alternatives et NG54 n'est pas payé une seconde fois. La source54 garde son littéral−sqrt(u/60) et sa borne volontairement plus faible−sqrtu/60.

**Décision :** conserver la correction locale et la dérivation quantitative comme diagnostic de raccord. Ne soumettre aucun Lean ordinaire pour une victoire : le morceau pertinent encore manquant est Γ*/TypeII avec sa comparaison globale aux vrais parents. Le test neuf demandé a un rôle de falsification strict, pas de preuve de contournement. Recherche active, score0, victoirefalse.
