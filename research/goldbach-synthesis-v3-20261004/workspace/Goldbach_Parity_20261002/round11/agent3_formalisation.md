# Boucle 11 — B6 certifié et audit indépendant B2–B13

**TERMINÉ. B6 compile réellement sans preuve incomplète ; victoire fausse.** Le fichier `lean/SquarefreeLcmCoefficient.lean` prouve le coefficient fini avec les vrais Möbius, totient, PPCM et diviseurs. Il ne suppose aucune estimation cible ni compensation manquante. L'audit écrit conserve les deux queues, la partie basse r<=alpha et le principal acquis de référence. Le moment bilatéral B13, le seuil BV supplémentaire et le pont couvert e restent ouverts.

## 1. Inputs, support et gate préalable

Le rapport 2 final a été lu et son SHA vérifié : `agent2_bilateral_compensation.md`, `ea3d4944f5a55df6eb9bbc30fed1fb90a00d24b2c505d196d8b61559394e9830`. Le `PROBE_BLOCK.md` de boucle11, `round10_feedback.md`, `round11_observe.md` et le prompt effectif `.arbor/sessions/parity/experiments/11.2/executor_prompt.md` ont été lus sans mutation Arbor. Les §§6.1–6.3 et12.2 de la monographie ont été relus. Le prompt dit lui-même que le workspace isolé est un chemin, sans dépôt Git ; aucun checkout ou ancien module n'a été modifié.

Le rôle6 a été sollicité directement. Avant tout appel compilateur, il a confirmé explicitement son gate B6 final sauvegardé :

```
ap_prefix.json      84d4cd68709aa9a16fd4a96d44374726c427b3cce40df9b364b1eae8c474d917
ap_prefix_checks.py b58ea3d4fc41ffb60c548a44e6f92bad2fc01d812bf3a4338d2b0d70d834f1c1
```

Le statut global est `PASS_NEW_FINITE_CONTRACTS_ONLY`, N=100000000, et `finite_coefficients.B6_guarded_finite_product.status=PASS_IDENTITY_ONLY`. Le produit P=3003=3*7*11*13 est carré-libre et unitaire à N ; les **seize** r|P sont vérifiés. Chaque tentative du builder recontrôle ces champs et le SHA du script contre `script_sha256` dans le JSON. Aucun ancien banc PASS n'est relancé par ce rôle.

Le support de B6 est d|P. Le support de la tête B2 est d<=D avec d²|m, et celui de B4 est une série infinie en d. Ces trois supports ne sont pas assimilés. r=9 est hors B6 parce que r ne divise aucun P carré-libre ; son coefficient infini nul relève de sa propre cancellation. r=5 non unitaire ne satisfait pas le wrapper unitaire pour N=10^8. Ces falsificateurs ne réfutent pas l'identité B6 générale dans ses gardes.

## 2. Preuve Lean arithmétique exacte

Le namespace `GoldbachRound11` travaille dans Q, corps exact naturel pour ces coefficients rationnels. L'égalité rationnelle donne les mêmes coefficients après plongement dans R ; aucune approximation numérique n'entre dans la preuve.

Le théorème `squarefree_lcm_coefficient` énonce littéralement

```
P squarefree, r|P ->
sum_(d|P) mu(d)/phi(lcm(r,d^2))
 = (1/r)*prod_(p in P.primeFactors, p nondivisor r)
                     (1-1/[p(p-1)]).              B6
```

`P.primeFactors` est le vrai ensemble des premiers de P ; mu est `ArithmeticFunction.moebius`, phi est `Nat.totient`, et lcm est `Nat.lcm`. Ni le produit ni la somme n'emploient un coefficient libre. r est carré-libre et positif parce que r|P et P est carré-libre. Le cas P=r=1 est inclus.

La preuve suit une normalisation réellement arithmétique :

```
f_r(d)=mu(d)*phi(gcd(r,d))/(d*phi(d)).
```

Elle établit les étapes suivantes sans les prendre comme prémisses :

- `totient_square` : phi(d²)=d*phi(d), y compris d=0.
- `totient_gcd_lcm` : phi(gcd(a,b))*phi(lcm(a,b))=phi(a)*phi(b) pour a>0, par les deux identités totient de produits et gcd*lcm=a*b.
- `gcd_square_of_squarefree` : gcd(r,d²)=gcd(r,d) pour r carré-libre, par le vrai lemme radical de divisibilité d'une puissance.
- `normalized_isMultiplicative` : f_r est multiplicatif. Les deux gcd sont premiers entre eux lorsque leurs arguments le sont ; totient et Möbius multiplient alors exactement.
- `normalized_eq_lcm` : f_r(d)=phi(r)*mu(d)/phi(lcm(r,d²)) pour d>0, avec tous les dénominateurs non nuls établis.
- `normalized_prime` : f_r(p)=-1/p si p|r, et -1/[p(p-1)] sinon.
- `primeFactors_filter_dvd` : les premiers de P divisant r sont exactement les premiers de r.

Le produit de `1+f_r(p)` est la somme de f_r sur les diviseurs de P par le théorème multiplicatif carré-libre mathlib. Sa partie p|r vaut phi(r)/r par la formule d'Euler réelle du totient. La division par phi(r) donne B6, sans hypothèse analytique.

Le wrapper `squarefree_lcm_coefficient_unit` possède **l'indicatrice extérieure** gcd(r,N)=1 et **le filtre intérieur** gcd(d,N)=1 de la référence finie. Sous gcd(P,N)=1, r et chaque d|P sont unitaires par divisibilité, et le filtre est démontré égal à l'ensemble complet des diviseurs. Aucune progression non réduite n'est créditée du principal 1/phi(q).

## 3. Compiler, erreurs réelles et axiomes

Le builder neuf `role3_build.py` utilise Lean 4.15.0 installé et exclusivement les oleans mathlib du cache local, sans téléchargement. Il compile **seulement** le nouveau module ; aucun custom olean antérieur n'est importé. Le reçu conserve version, LEAN_PATH, arguments complets, code de sortie, hashes, source de chaque tentative en `.txt` et log intégral.

| Tentative | Résultat | Diagnostic réel |
|---|---|---|
| 01 | Lean exit1 | Après clearance des dénominateurs, nlinarith ne réduisait pas la lambda de `congrArg` dans la normalisation. `dsimp only at hm` expose son identité polynomiale. Les autres lemmes étaient élaborés. |
| 02 | Lean exit0 | B6 et le wrapper extérieur initial sont certifiés. |
| 03 | Lean exit0 | Le wrapper est précisé avec son filtre **intérieur** d unitaire. La source finale compile sans erreur ni avertissement. |

Le `sorryAx` du log01 est le placeholder automatique d'une preuve en erreur, non une balise introduite dans le code. Le log03 final imprime les axiomes de chacune des neuf conclusions, uniquement

```
[propext, Classical.choice, Quot.sound].
```

Le fichier final ne contient aucun token `sorry`, `admit`, déclaration `axiom` ou `native_decide`. Le minorant G>=0 n'a jamais été soumis au compilateur. L'erreur01 est une erreur de tactique réparée, pas un diagnostic du mur de la parité.

```
SquarefreeLcmCoefficient.lean  f791b4be0f731244a44449f27bb236c7890a8265c0e7fa6d55150a1a230e1ba6
SquarefreeLcmCoefficient.olean 7ae468c5f94b93113c6cbbd90464509ba9bda67f286bd61df4d5134042bdc2af
role3_build.py                 8641ef1026c82307b325d2a629d30323539b54b564365e5d663d8e168f719d9f
role3_build_receipt.json       cc9510fbd512314e5bb79a5dd097341b826097a6c7f0bd9686c57e5e1b0b9123
attempt03.log                 6fe78585da6cfe8564351653b7603a1020c735b390739c2f578f1aed05c690fc
```

## 4. Audit B2/B3 : tête, queue, AP et intersections

La décomposition mu(m)^2=F_D(m)+R_D(m) est complète. La tête F_D ne porte aucun facteur mu(m)^2 supplémentaire. Sur Lambda_N(N-m) non nulle, gcd(m,N)=1 ; tous r|m et d²|m sont donc unitaires. Cela justifie les deux filtres N de B2, puis q=lcm(r,d²). Avec X=N-1, m>=1 est exact ; n=1 ou0 ont Mangoldt zéro et aucune masse m=0 n'est complétée. Une sélection E de n doit être la même dans chaque Psi_E du banc fini.

Pour r,d carrés-libres, g=gcd(r,d), b=d, c=r/g donnent gcd(b,c)=1 et q=b²c. Chaque q cube-libre possède ce b et c uniques. Le coefficient est bien mu(b)mu(c)sum_(g|b,cg<=a)mu(g)log(cg), avec **tous** les cg<=a, sans front inférieur alpha. La collision r=d=3 donne q=9,phi=6 ; le faux produit rd²=27 donne phi=18. Sur m=927, n=99999073 premier, 9|m et 27∤m : l'erreur touche la vraie AP, pas seulement un coefficient abstrait.

Le témoin m=3*3217²=31047267, n=68952733 premier, garde U_a=-log3. Pour D<3217, la tête d=1 donne -log n log3 et la queue d=3217 donne +log n log3 ; leur somme restitue le zéro entier mu(m)^2. Une multiplication de la tête seule par mu(m)^2 détruirait B2. Le gate conserve précisément ce falsificateur.

## 5. Audit B4–B7 : infini, convolution et principal bas

À r fixé, la série B4 est absolument convergente. Les intersections sont absorbées dans un facteur fini dépendant de r, et la série positive sum_d mu(d)^2/[d phi(d)] converge par son produit eulérien. Son masque extérieur gcd(r,N)=1 est conservé. Il serait faux d'accorder la formule non masquée à r divisant N.

Pour r carré-libre unitaire, les facteurs locaux sont 1/p si p|r, et 1-1/[p(p-1)] sinon, d à base p|N étant exclu. Ils donnent bien B5 avec g_p=(p-1)/(p²-p-1). Si p²|r avec p∤N, les deux exposants d=1 ou p ont le même exposant du PPCM et s'annulent ; le coefficient infini est zéro. B6 peut fournir ces facteurs après limite **absolument convergente**, mais ne paie pas le passage de d<=D à la série : c'est B9.

La convolution de c_N(r)=mu(r)1_{gcd(r,N)=1} prod_(p|r)g_p avec mu(r)/r a exactement les coefficients h'_N affichés. Pour p∤N,

```
1-p*g_p=-1/(p²-p-1),
h'_N(p^j)=-p^(-j)/(p²-p-1), j>=1.
```

Pour p|N, h'_N(p^j)=p^(-j). Puisque N est pair, les p∤N ont p>=3 et p²-p-1>=p-1. Les valeurs absolues de h'_N sont donc dominées terme par terme par h_N acquis au §12.2. Les moments (50), leur split et les préfixes Mertens ordinaires (51)/(52) peuvent être repris pour cet autre coefficient fixe ; aucune corrélation mu*Lambda mobile n'est estimée ainsi.

Le principal de V_N sum h'_N est S(N). Pour p∤N, le facteur devient p(p-2)/(p-1)^2 ; pour p|N, p/(p-1), y compris le facteur2. La somme logarithmique entière exige l'endpoint `log(a)A'_a` avec W'_a. V_N<=1 et la domination des moments permettent la même enveloppe G54/u sous a>=N^(1/5), a<N, u>=10^6. Le véritable exposant source est -sqrt(u/60) ; l'exposant -sqrt(u)/60 employé est un affaiblissement explicite, pas une citation littérale.

Ainsi B7 conserve le principal **-S(N)** de sum_(r<=a)mu(r)log r A_N(r). Après AP, le principal de T_a^Lambda est -S(N)(N-1). Remplacer N-1 par N coûte S(N). Les r<=alpha sont présents : m=11 a un bas -log11 et un annulus nul, tandis que m=411 a le bas -log3 annulé par l'annulus +log3. Un contrôle du seul annulus ne paie pas le préfixe entier.

La source définit déjà j_alpha=-U_alpha, J_ref et E_J=S(N)N-J_ref. Le calcul B4–B7 retrouve cette référence au front a ; ce principal acquis n'est ni un nouveau gain de parité ni une quantité effaçable.

## 6. Audit des deux queues B8/B9 et de B10/B11

Pour D>=1, L_D=1+log D>=1. La queue physique B8 utilise |U_a(m)|<=u tau(m), Lambda_N<=u, puis tau(d²v)<=tau(d²)tau(v). Pour d carré-libre, tau(d²)=d_3(d). Le compte v<=N/d² est un compte exact de multiples positifs, et sum_(v<=x)tau(v)<=x(1+log x). Il ne supprime pas un +1 d'une AP générale.

La sommation dyadique de d_3(d)/d² donne

```
sum_(d>D)d_3(d)/d²
 <= (4L_D²+16L_D+24)/D <=44L_D²/D.
```

Les séries utilisées sont 2,4,12 pour 2^-j, (j+1)2^-j et (j+1)^2 2^-j. Les constantes B8 sont donc cohérentes : 44Nu²(1+u)L_D²/D.

La queue principale B9 est un autre poste. Pour r,d carrés-libres, phi(lcm(r,d²))=phi(r)d phi(d)/phi(gcd(r,d)). Avec r=gh, g|d et gcd(h,d)=1, le réciproque vaut 1/[phi(h)d phi(d)]. Il y a au plus tau(d) choix de g et sum_(h<=a)1/phi(h)<=3(1+u). Les filtres unitaires sont supprimés seulement dans ce majorant positif.

Pour la série restante, d/phi(d)<=3(1+log d) et sum_(d<=x)tau(d)<=x(1+log x). Les deux facteurs logarithmiques donnent le même polynôme dyadique, avec le facteur3 : la queue est <=132L_D²/D. Le facteur extérieur3 explique **396** dans B9. Il n'y a pas de troisième puissance de log D cachée. On retrouve 396Nu(1+u)L_D²/D, distincte de B8.

Dans B10, les moduli sont unitaires et |w|<=u tau(q). L'all-prefix BV de Lambda ordinaire s'applique après l'expansion exacte, avec ses poids fixes en n. Il ne s'applique pas à mu(m)Lambda(n). La différence Psi_N/Psi ordinaire garde les bases p|N ; sur n=p^j<=N-1, z=N-p^j est positif. La somme intérieure sur q|z est <=u sum_(q|z)tau(q)<=u tau(z)^2. Le majorant tau(z)<=2^2040 z^(1/8) et sum_(p|N,j)log p<=u omega(N)<=u²/log2 donnent bien la charge 2^4080 N^(1/4)u³/log2. Les properpowers à base unitaire restent dans Psi_N.

Avec D=floor(N^(1/64)), a=ceil(N^(7/16)), q<=2N^(15/32). La troncature de tau, son second moment d_4 et BV all-prefix ont la même portée **qualitative éventuelle** que dans le head9. Le seuil BV et ses constantes ne sont pas évalués ; aucune validité automatique dès u=10^24 n'est déduite. Les +1 généraux restent dans l'erreur AP avant toute absorption justifiée.

B11 assemble correctement B8+B9+E_AP+NG54/u+S(N), après main X=N-1. Il s'agit d'un défaut de référence de la forme déjà prévue par E_J source. Cette enveloppe ne paie pas B13 et n'est pas une nouvelle borne de D_N.

## 7. Audit B12/B13 et contrat encore nécessaire

Le vrai poids est G_N(m)=mu(m)^2 Lambda(m)+S(N)mu(m). La première composante annule les propres puissances du **second** axe ; la première Lambda_N conserve les properpowers unitaires. Sur m=483=3*7*23, n=99999517 premier unitaire, mu(m)=-1 et Lambda(m)=0. Ainsi G_N(483)=-S(N)<0, avec positivité de S(N) acquise. Le minorant pointwise G>=0 est donc **rejeté avant compilation**. Aucune tentative Lean ne porte ce faux théorème. Ce témoin ne prouve pas une impossibilité globale des méthodes bilatérales.

La partition F_N=F_unit+F_nonunit garde les vraies bases premières divisant N et leurs signes. Avec R_unit=sum Lambda_N(n)mu(m)^2 Lambda(m), B13 est exactement

```
R_unit+S(N)F_unit-S(N)N
 = sum_(n<N)Lambda_N(n)G_N(N-n)-S(N)N.
```

Le signe de l'obligation est une **minoration** de ce moment pour obtenir une majoration du bracket après référence. BV de Lambda seule ne minore ni le moment couplé ni sa composante prime-paire. Les p,q contraints premiers, les nonunités et les quatre Möbius HH restent nécessaires. La native phase1 sur q|k n'ajoute aucune oscillation.

Pour le raw n=p^j unitaire, la mobilité singulière porte le dénominateur p-2, pas n-2. Regrouper les exposants j donne une masse <=u pour chaque base p, puis sum_(p>=3)1/(p-2)<=1+u. La charge S(N)u(1+u) annoncée est donc un majorant positif valide. Elle ne paie pas le principal signé B13. En particulier m=1 a G_N(1)=S(N) alors que le modèle court est vide : un principal global ne peut être substitué sur cette face sans son coût.

Le raccord R_unit=R_sf+P_ret-T_pairs, puis F_nonunit signé, conserve Proposition6.2. Il ne supprime ni F_N ni le pont couvert. Une candidature gagnante demanderait une minoration indépendante du vrai B13, avec le raccord à B11, modèle couplé, coins et autres postes du déficit. L'écrire comme prémisse serait reprendre la demande dans les hypothèses.

Le ledger choisi demeure

```
D_N=B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}
       +I_alpha+2max(e,0).
```

Pas de crédit additionnel pour B_H ou pour la référence, pas de second paiement des properpowers/I/Z_face. L'onset source demeure u>=10^24 ; le seuil BV supplémentaire et e sont ouverts. Les identités auxiliaires et les analyses écrites ont des statuts séparés.

## 8. Conservation et décision

Le helper neuf de conservation11 a été importé par chemin explicite sans bytecode. Il confirme **405** artefacts protégés inchangés, dont les 64 fichiers finaux de round10, PNG/olean et PDF/ZIP originaux. Registre SHA `f86a31f72d624124338afad6932cd859dceae164a6f3422f9b8998164fcf9e05`. Aucun ancien banc ni builder n'a été exécuté et aucun custom olean antérieur n'a été importé. Les seules écritures de ce rôle sont sa source nouvelle, son builder/logs/snapshots/reçus et le présent rapport.

Classification : `COMPILED_ACTUAL_FINITE_LCM_COEFFICIENT`, `REFERENCE_PRINCIPAL_AND_LOW_PREFIX_PRESERVED`, `B8_B9_DISTINCT_WRITTEN_BOUNDS_VALID`, `WEIGHTED_BV_ONSET_UNEVALUATED`, `BILATERAL_SIGNED_MOMENT_OPEN`, `COVERED_BRIDGE_OPEN`, `VICTORY_FALSE`. Score sémantique : 0. Le Juge indépendant reconstruira la source finale et vérifiera chaque conclusion ; B6 seule n'accorde aucune victoire.
