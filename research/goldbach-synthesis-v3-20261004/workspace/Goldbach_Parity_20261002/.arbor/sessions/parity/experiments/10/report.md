# Boucle 6 — audit du contrat de la vraie fibre à deux carrés

Agent 4, 2 octobre 2026. Document proposé audité : `agent2_coupled_squarefree.md`, formules S1–S14. La version proposée reste conservée comme trace ; les corrections ci-dessous font autorité pour son test. Il s'agit d'un audit mathématique des hypothèses, sans nouvelle compilation Lean.

**Verdict : rejet avant compilation du contrat S3 → S4 tel qu'écrit, et du transfert favorable fondé sur la longueur brute.** S2, avec toutes ses congruences, reste une identité exacte. Le CRT corrigé ne fournit aucune borne nouvelle du signé HH complet. PV est une borne valide dans son domaine ; son insuffisance ici n'est ni une falsification de PV ni une impossibilité générale des méthodes de caractères. Aucune victoire n'est revendiquée.

## 1. Fibre originale et hypothèses indispensables

Le gelage conserve exactement

`A=b*u*v`, `C=k*s*t`, `A*x+C*zeta=N`, `x,zeta>0`,

avec le signe extérieur **mu(u) mu(v) mu(s) mu(t)**. On conserve `u,v,s,t>y`, les deux détecteurs carrés-libres, `I_W(n)`, `gcd(n,N)=1`, `n=A*x`, `m=C*zeta`, `r=s*t*zeta`, `k<=Q`, `r>alpha`, toutes les faces et les logarithmes. Le module CRT original reste `a*r`, non le conducteur du caractère ni le produit des quatre indices signés. S1 décrit une composante à twist isolé ; l'identifier à une projection HH complète exige ses facteurs de caractères réels.

Sur une fibre originale non nulle, A et C sont carrés-libres et il faut écrire explicitement **gcd(A,C)=gcd(A,N)=gcd(C,N)=1**. La seule notation `gcd(A,C*N)=1` ne contient pas la dernière condition. Celle-ci est bien héritée des unités originales : `gcd(n,N)=gcd(m,N)=1` et `C|m`. Elle est indispensable pour l'équivalence `gcd(N-C*zeta,N)=1 iff gcd(zeta,N)=1` utilisée dans S1. Aucun acquis n'est modifié ; son hypothèse doit être conservée dans l'énoncé.

Pour des caps entiers, les cinq fronts du §2 sont corrects : `r>alpha`, `x>=1`, `a<=m`, `b<=m` et `a>U` donnent respectivement les bornes écrites. Le dernier front utilise que a est entier. Toute autre fenêtre reste littérale. Sur le support `W>=V_original`, le poids `log(b)*log(s*t*zeta)` est celui de la continuation fournie. Les quatre signes ne peuvent être remplacés par un coefficient arbitraire ou par le signe d'un seul H.

## 2. Faux contrat d'inversion et contre-exemple exact

S3 oublie **gcd(d,ell)=1**. Les conditions S3 seules n'impliquent donc pas `gcd(C*f*d^2,lcm(A,e^2,ell))=1`.

Le témoin entier à N=100000000 est

`A=273=13*3*7`, `C=10403=101*103`, `q=5`,
`d=11`, `ell=11`, `e=f=1`.

A et C sont carrés-libres, mutuellement premiers et premiers à N ; tous les tests S3 écrits sont vrais. Pourtant

`M=lcm(273,1,11)=3003`, `B=f*d^2=121`,
`gcd(C*B,M)=11`, `N mod 11=1`.

La cellule est vide : `11|zeta` et `11|N-C*zeta` imposeraient `11|N`. L'inverse `(C*B)^(-1) mod M` est donc illégal. Ce n'est pas une erreur du compilateur : le contrat arithmétique favorable est faux et doit être éliminé avant compilation. L'intervalle positif de la fibre n'est pas vide, puisqu'il autorise `1<=zeta<=floor((N-A)/C)=9612` ; c'est cette cellule précise qui est incompatible.

La correction directe des cellules retenues est

`S3' = S3 and gcd(d,ell)=1`,

en conservant les hypothèses structurelles du §1. Alors d est premier à A, e, K et ell ; f divise rad(K), donc est premier à A, e et ell ; C est premier à A, e et ell. Par conséquent **gcd(C*B,M)=1**. De plus `gcd(M,q)=gcd(B,q)=1`. S4 et S5 sont ensuite exactes. Le retrait de la cellule d/ell commune est justifié par son incompatibilité, pas par une annulation présumée.

Une version générale évite toute exclusion implicite. Avant S3, poser

`L=lcm(d^2,f)`, `M=lcm(A,e^2,ell)`, `g=gcd(C*L,M)`.

Les conditions sont exactement `zeta=L*v` et `C*L*v=N (mod M)`. Si `g` ne divise pas N, la contribution est zéro. Sinon poser `M'=M/g` et

`v0 = (N/g)*(C*L/g)^(-1) mod M'`,
`zeta=L*(v0+M'*j)`.

L'inverse existe alors ; le cas `M'=1` prend `v0=0`. Dans S3', `gcd(d,f)=1`, donc `L=B` et `g=1`, ce qui donne précisément S4. **Le produit f*d² n'est pas permis avant cette coprimalité.**

e peut partager A. Exemple conservé : même N,A,C, mais `d=f=ell=1,e=3`. On obtient `M=lcm(273,9)=819`, `v0=107`, et 12 valeurs dans `1<=zeta<=9612`, commençant par 107,926,1745. Le pas n'est pas `A*e²=2457`.

## 3. Ordre des suppressions et inclusion-exclusion

S2 est exacte, finie, et conserve d=1 lorsque zeta=1. Les restrictions de S3' ont des justifications distinctes ; leur ordre doit être visible dans le théorème et le programme.

| Restriction | Justification autorisée |
| --- | --- |
| gcd(d,A)=1 | La relation A\|N-C*zeta et les unités structurelles imposent gcd(zeta,A)=1, avant toute inclusion-exclusion. |
| gcd(d,K)=1 | Garder d'abord le masque exact gcd(zeta,K)=1, supprimer les d interdits, puis développer ce masque en f. |
| gcd(e,C)=gcd(ell,C)=1 | n=N-C*zeta est toujours premier à C puisque gcd(C,N)=1. |
| gcd(e,N)=gcd(ell,N)=1 | Garder d'abord le masque unitaire exact ; le supprimer par inclusion-exclusion seulement après ce regroupement. |
| gcd(d,e)=1 | Si un premier divise zeta et n, il divise N ; le masque exact l'exclut. Après gcd(d,K)=1, une paire commune est directement incompatible. |
| gcd(d,ell)=1 | Après gcd(d,K)=1, un premier commun imposerait qu'il divise N, contradiction. La cellule est vide. |
| gcd(f,q)=1 | Chaque cellule avec un premier commun à f et q a chi(zeta)=0 puisque f\|zeta. |

Ces restrictions ne disent pas que chaque terme de la version **entièrement développée** est nul. Un exemple à la même fibre est `zeta=1472`, `n=84686784`, `d=1,e=2,ell=1`. On a A\|n et e²\|n, chi5(zeta)=-1. La cellule f=1 est non nulle isolément ; le masque exact élimine zeta, et les termes f=1 et f=2 de son inclusion-exclusion se compensent. Prendre les valeurs absolues avant cette compensation, ou supprimer une seule de ces cellules, détruirait l'identité. Toute tête tronquée doit être définie avec les masques exacts avant leur développement ; les restrictions restent alors valides. L'expansion originale générale permet un contrôle direct sans ces suppressions.

## 4. Le produit de caractères complet reste principal

Après S3', le twist **isolé** de S5 satisfait bien

`chi(v0+M*j)=chi(M)*chi(j+c)`, `c=v0*M^(-1) mod q`,

et sa somme sur q indices consécutifs est nulle pour un caractère nonprincipal. Cette propriété ne s'étend pas automatiquement au produit sur les deux axes.

Pour q\|N et des arguments unités,

`chi(N-C*zeta)*conj(chi(zeta))=chi(-C)`,

et le produit complet réellement écrit dans S6b est

`chi(A)*chi(x)*conj(chi(C))*conj(chi(zeta))`
`=chi(n)*conj(chi(m))=chi(-1)`.

Les valeurs de chi sur les unités ont norme 1. Ce produit est donc constant et non nul ; **chi(x) ne peut être supprimé au gelage**. Pour chi5 quadratique, chi(-1)=1 ; sur les unités modulo 5 ce secteur a somme 4, tandis que la somme du twist isolé sur les cinq résidus est zéro. Un secteur avec d'autres facteurs n'est pas assimilé à S6b sans audit, mais le secteur compensateur S6b ne bénéficie d'aucune oscillation PV. Si l'on sort du support unitaire, le produit devient `chi(-1)*|chi(m)|²`, ce qui impose encore le détecteur unitaire ; la constante non nulle ne peut être prolongée hors support.

## 5. Poids, queues et coût extérieur

S7 est une majoration brute valide après correction des cellules. L'Abel sur la progression paie `sup|F|+Var(F)` : un sélecteur arbitraire borné n'a pas une variation polylogarithmique garantie. Le nombre de cellules `D*E*2^omega(K)*2^pi(W)` ne disparaît pas. S8 est une substitution **conditionnelle** aux deux poids de Rosser et à leur entrée analytique ; elle paie le reste positif, sa densité et `L_sieve`. Pour l'application après suppression positive de la fibre A, les densités locales sont delta(p)=0 pour p\|C et 1 sinon. Elles satisfont le même majorant de dimension 1 ; les erreurs de plancher de chaque ell coûtent O(1). Cette substitution n'est ni une identité du moment tordu ni une borne nouvelle du signé HH.

S9 est exacte. Dans S10, compter les progressions d²\|zeta avec d premier à A donne `O(X/(A*D))+floor(sqrt(Z))` : un +1 est payé pour chaque d. Dans S11, A carré-libre impose `e²/gcd(e,A)|x`; C est premier à e. La somme `sum_(e>E)gcd(e,A)/e²` est `O(tau(A)/E)`, en utilisant `gcd(e,A)=sum_(h|e,h|A)phi(h)`. Les e partageant A ne sont pas supprimés. On conserve le terme `floor(sqrt(N))`. S12 est donc une borne sûre sur les autres sélecteurs exacts, avec `|a_D|<=tau(zeta)<=T_N`. Aucun +1, moment divisoriel ou nouveau moment de Rosser n'est absorbé sans preuve.

**Correction supplémentaire de S13 :** le nombre littéral de points d'une fibre est au plus `1+X/A`, pas X/A. La quantité `L_cont=N/(A*C)=N^(.5-sigma-nu)` est sa longueur continue. La formule « nombre de fibres fois longueur est N » ne paie le nombre de points par ce produit que dans les sous-boîtes où L_cont est grand, ou avec un comptage global supplémentaire des fibres actives. Quand `sigma+nu>=.5`, le +1 peut dominer et ne peut être abandonné. Exemple original admissible à N=10^8 : `A=273,C=99999727,x=zeta=1,b=13,u=3,v=7,k=1,s=7951,t=12577,y=W=2`. Il conserve unités, carré-libres, core, cap et r>100 ; N/(A*C)<1, mais il contient un point. Ce témoin ne se prétend pas une boîte équilibrée asymptotique.

Dans la sous-boîte revue où la longueur est grande, `sigma,nu>2z` impose `L_cont<N^(.5-4z)` ; aux conducteurs de taille N, PV coûte sqrt(N)log(N), plus que la longueur pertinente. Aux cellules d,e,f,ell, le pas peut seulement réduire encore le nombre de points. Les calculs d'exposants S14 sont corrects comme **coûts de majorations optimistes**, avant les masques et avec une longueur continue positive ; ils ne sont pas des minorations du vrai signé. Le coût des +1 renforce les obligations laissées ouvertes. Pour z=1/16, L_cont<N^.25 ; le théorème premier de Burgess cité ne donne pas non plus de gain relatif à cette longueur. Ni ce constat ni S14 n'excluent un autre regroupement signé des A,C ou un autre régime de paramètres.

## 6. Gate de la boucle

Le candidat a deux rejets différents :

1. **S3 → S4 sans compatibilité d/ell : faux énoncé exact**, témoin entier ci-dessus ; rejet avant compilation et corrigendum S3'.
2. **Gain HH complet importé du twist isolé ou de la longueur brute : transfert non obtenu**. La vraie fibre, le secteur compensateur, les queues, la variation et les coûts extérieurs restent à payer. La validité des identités corrigées ne les estime pas.

Zeta=1 reste présent et n'est pas crédité comme négligeable ; sa borne sectorielle d'amplitude antérieure reste conditionnelle à la même entrée Rosser et ne ferme pas le budget terminal. Aucune borne indépendante du reste signé complet, des grands conducteurs ou de D_N n'a été dérivée. Aucun nouveau fichier Lean auxiliaire n'a été produit pour remplacer cet objectif ; aucun verdict de compilation n'a été inventé. Les sources et certificats antérieurs restent acquis et inchangés.

Sources primaires consultées : [Montgomery–Vaughan, th.9.18 et 9.27](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf), [Motohashi, identité de Rosser et lemme fondamental](https://www.math.utoledo.edu/~codenth/Spring_13/3200/NT-books/Lectures_on_Sieve_Methods_and_Prime_Number_Theory-Motohashi.pdf). Leur emploi est limité aux majorants et hypothèses indiqués, sans import comme axiome Lean.
