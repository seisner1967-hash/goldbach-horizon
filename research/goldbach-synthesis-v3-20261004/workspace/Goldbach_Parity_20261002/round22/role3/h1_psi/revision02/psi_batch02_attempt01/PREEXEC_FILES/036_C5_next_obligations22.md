# C5 — obligations analytiques suivantes, SOURCE/PAPIER

Cette feuille ne définit aucun théorème conditionnel tenant P1, Fubini ou
χ′/χ en prémisse. Elle décrit la prochaine vraie preuve à écrire après le gel
du paquet ψ54, en conservant le contour et Arch originaux.

Pour −1<Re s<0, poser A=(1−s)/2, C=1−s/2 et B=1+s/2, tous de partie réelle
positive. La duplication déjà rédigée donne

    ψ(A)+ψ(C)=2ψ(1−s)−2log2.

La réflexion de Γ et sa récurrence doivent donner l'identité réelle

    Γ(C)Γ(B)=(s/2)π/sin(πs/2).

La valeur s/2 est non nulle. Le sinus est non nul sur cette bande, à déduire
de la caractérisation exacte de ses zéros. La dérivée logarithmique de cette
identité entre fonctions véritables donne

    −ψ(C)/2+ψ(B)/2=1/s−(π/2)cot(πs/2).

La dérivée du vrai χ et ces deux identités doivent donc fournir

    χ′(s)/χ(s)=logπ+1/s−ψ(A)/2−ψ(B)/2.

Sur s=−1/2+it, A et B ont partie réelle 3/4. P1 et u=2v produisent un seul
noyau entier, sans séparation de termes divergents en v=0 :

    K(t,v)=[exp(−3v/2+itv)+exp(−3v/2−itv)−2exp(−2v)]/(1−exp(−2v)).

Le numérateur vaut 0 en v=0. Pour v≥0, les normes des trois dérivées sont
majorées au total par 7+2|t|. MeanValue fournit donc une norme≤(7+2|t|)v.
Pour 0<v≤1, exp(2v)≥1+2v donne

    1−exp(−2v)≥2v/(1+2v)≥v/2,
    |K(t,v)|≤14+4|t|.

Pour v≥1, exp(2)>2 donne le dénominateur≥1/2 et

    |K(t,v)|≤8exp(−3v/2).

La vraie borne Γ sur la droite gauche doit encore être liée à G :
|G(−1/2+it)|≤4Y^(−1/2)exp(−π|t|/4). Elle donne le dominateur mixte concret

    4Y^(−1/2)exp(−π|t|/4) ·
      [(14+4|t|)1_(0,1](v)+8exp(−3v/2)1_(1,∞)(v)].

Chaque facteur est effectivement intégrable. Avant Fubini, payer la
mesurabilité du vrai intégrande et les integrability sur le produit restreint,
au lieu d'introduire une hypothèse générale nommée majorant.

Après l'inversion Mellin payée indépendamment, la dernière intégrale est

    B_Y=∫_(v>0)[e^(−v)f_Y(e^(−v))+e^(−2v)f_Y(e^v)−2e^(−2v)f_Y(1)]
                         /(1−e^(−2v))dv.

Le transport x=e^v vers x>1 doit donner
B_Y=Arch_Y−∫_(x>1)f_Y(x)/x dx+2log2·f_Y(1). L'intégrale de
e^(−v)/(1+e^(−v)) vaut log2 ; sa preuve doit payer substitution et primitive.
Les intégrales de f_Y/x sur (0,1) et (1,∞) valent respectivement
1−exp(−1/Y) et exp(−1/Y). Leur somme réelle égale1, d'où le signe −1 final.

Tout ceci reste PAPIER, sans compilation, numérique ou crédit C5/global/D_N.
