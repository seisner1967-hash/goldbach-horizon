# Équivalences exactes et coût théorique — SOURCE seulement

## Extrémités dyadiques

Soit S=2^512. Pour un rationnel exact p/d avec d>0, les anciennes conversions Fraction/floor/ceil et les nouvelles conversions entières donnent toutes deux [floor(pS/d),ceil(pS/d)]. Python `n//d` calcule floor(n/d), même lorsque n ou d est négatif ; `-((-n)//d)` calcule ceil(n/d) pour tout entier d≠0.

La multiplication scalaire d'une Box [l,h] par p/d se décrit par les extrêmes de p*l et p*h avant division par d>0. Le minimum et le maximum sont pris avant l'arrondi. Pour une division de deux intervalles dont le dénominateur exclut zéro, les quatre quotients exacts aS/b des extrémités sont les mêmes que dans la voie Fraction. Pour un ensemble fini, floor(min q)=min floor(q) et ceil(max q)=max ceil(q). Ces identités paient les quatre formules entières de `Box.rational`, `Box.scale`, `Box.__truediv__` et `Box.widen`. Les gardes de dénominateur et de rayon négatif restent effectives.

La multiplication de Box était déjà une opération d'entiers dans l'ancien fichier et reste inchangée. Aucune amélioration n'est revendiquée sur cette opération.

## Transport du catalogue

Ancienne représentation : e=R/S, e_q=E/S, avec R,E entiers≥0 et U entier positif. Le milieu des deux coordonnées et leur rayon L1 sont les mêmes dans les deux voies. Après multiplication des milieux, soit P l'entier
|raw_real−rounded_real*S|+|raw_imag−rounded_imag*S|.
L'erreur exacte du produit est P/S² ; la garde effective est P≤2S. La récurrence ancienne avant arrondi donne

c=(1+E/S)R/S+U E/S+P/S²
 =((S+E)R+U E S+P)/S².

L'arrondi dirigé sur la grille donne donc exactement
R_next=ceil(((S+E)R+U E S+P)/S).
La source entière met en œuvre cette formule. Le supplément vérifié est
0≤R_next*S−((S+E)R+U E S+P)≤S,
soit un supplément≤1/S pour le rayon réel.

La garde800 e_q≤1/2 est équivalente à1600E≤S. Par le majorant binomial/géométrique (1+e_q)^800≤2, la même enveloppe fermée est
e≤2e_0+1600(Ue_q+3/S),
soit R≤2R_0+1600(UE+3). Le produit, l'arrondi et les non-annulations de toutes les primitives restent payés ; cette transformation n'injecte aucun rayon libre.

La construction de `box()` donne directement les extrémités centre±R. Elle est équivalente à élargir une Box ponctuelle par le rayon R/S. Le diagnostic cumulé de produit demeure ΣP/S². Le diagnostic de supplément est majoré par un EPS par transition, comme la voie originale. Le compteur `point_product` est incrémenté une fois par transition.

L'API `advance()` ne retourne plus la Box après mutation. Les deux appels concrets (`track.advance()` et `ytrack.advance()`) ignorent déjà cette valeur. Les échantillons suivants utilisent `box()` explicitement. Il n'existe pas d'autre appelant de CatalogueTrack dans les neuf sources. Le transport primal historique garde sa propre API et sa propre récurrence.

## Gamma et constantes

La projection valeur seule reproduit, dans le même ordre, toutes les opérations de valeur de `_stirling_log_and_derivative` : w=z+64, Log(w), w^−1, w^−2, les32 termes B_(2k)/(2k(2k−1)w^(2k−1)), puis le même élargissement4/(63·6^64). Elle ne construit pas les32 produits `power*inverse` de la dérivée. Gamma conserve sa réduction k log2, son exponentielle réduite, ses64 facteurs et sa division certifiée. Le calcul de psi/γ_E conserve la projection dérivée et les64 récurrences concrètes.

Le cache log(2π)/2 stocke uniquement les deux entiers d'extrémité de l'expression originale. Le cache f(1) fait de même pour `exp_box(Box.rational(-1/10000)).scale(1/10000)`. Chaque usage retourne une Box neuve, sans partage d'objet mutable. Les caches sont initialement vides et ne peuvent lire un ancien résultat. Le producteur exige des compteurs nuls au départ et exactement1,1,204800 à la fin. Les nombres de calculs ζ, Gamma, psi, Arch et de graines EM demeurent204800,204800,1,12288,32512.

## Comptes, sans mesure du candidat

Le banc actif a réellement atteint70400 nœuds en2931.282s au2026-10-03T13:52:03.371556UTC, avec210701647 octets d'artefacts ; il n'avait alors aucun verdict global. Ce checkpoint provient de son log en lecture seule c8c2b9. Sa limite3600s reste active. La projection linéaire vers204800 nœuds n'est pas une mesure d'achèvement ni une garantie.

Ce candidat retire théoriquement :

- les constructions répétées de log(2π)/2 sur les204800 appels Gamma (204799 répétitions, plus le calcul constant de psi qui partage désormais le cache) ;
- 32·204800=6553600 produits complexes de la seule dérivée Stirling inutilisée par Gamma ;
- les12287 reconstructions répétées de f(1) dans Arch, plus sa reconstruction ultérieure pour le terme constant ;
- les constructions Fraction/normalisations de la récurrence CatalogueTrack et les26181632 Boxes immédiatement jetées après `advance()`.

Le partage des128 phases était déjà présent dans la source originale ; aucun nouveau gain n'est attribué à ce partage. Les expressions Bernoulli et les constantes analytiques restent produites par la nouvelle invocation. Aucun gain temporel, pic mémoire ou temps complet du candidat n'est mesuré. La revue indépendante doit vérifier l'équivalence de ses cinq fichiers avant tout futur contrat exécutable.
