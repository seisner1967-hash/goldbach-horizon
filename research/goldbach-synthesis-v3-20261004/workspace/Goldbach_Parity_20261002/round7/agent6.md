# Agent 6 — reçu final boucle 7

2 octobre 2026. Tous les bancs fixent **N = 100 000 000**. Les PASS valident les identités finies et leurs falsificateurs ; ils n'établissent aucun gain asymptotique ni borne sur D_N. Les artefacts antérieurs sont préservés.

## Couverture logarithmique complète

`logarithmic_checks.py` / `logarithmic.json` vérifient coefficient par coefficient `μ(m)log(m) = -(μ*Λ)(m)` sur **19999 entiers m = 2..20000**, avec **65533 termes p^j**. Chaque log(m) est représenté par ses exposants dans les logarithmes des premiers. Puissances propres, termes p|ell, ell = 1 et μ(ell) nuls restent dans les domaines déclarés.

L'insertion dans le vrai profil raw est testée sur X = 303, 1024 : respectivement 802 et 2952 termes, dont 218 et 771 puissances propres. À chaque m, le numérateur convolutif entier est comparé après multiplication par le dénominateur commun log(m)>0 ; son rapport exact est ensuite récupéré de ses coefficients pour reconstruire le préfixe. Aucun quotient de logarithmes flottants n'est utilisé. F_N(1)=0 est conservé explicitement ; l'identité divisée ne s'applique qu'à m>1. L'extérieur des préfixes reste non calculé.

La réduction L2 aux seuls premiers avec **p∤ell** est également testée coefficient par coefficient sur ces 19999 entiers. Elle vaut après l'annulation des puissances. Remplacer Λ par les seuls premiers sans p∤ell est faux sur les carrés actifs 841 et 10201 : le terme partagé j=1 survit alors sans son compensateur j=2.

Les diagnostics imposent les secteurs qui seraient perdus par une suppression :

* m = 303 conserve (p,ell) = (3,101),(101,3), avec p∤N.
* m = 311 prime a F_N(311)>0 ; son unique secteur ell = 1 vaut exactement −F_N(311)<0.
* m = 841 = 29² a F_N(841)>0. n = 99999159 = 3*13²*59*3343 est non carré-libre et demeure actif dans le raw. Les termes d = 29,ell = 29 et d = 841,ell = 1 ont poids −1/2,+1/2 avant le signe global et s'annulent.
* m = 10201 = 101² a F_N(10201)<0 et la même annulation −1/2,+1/2. Supprimer les puissances propres créerait une contribution non nulle dans les deux exemples alors que μ(m)=0.

Le raw garde rho1, sans nouveau μ(n)². Les signes viennent des intervalles rationnels artanh déjà certifiés dans round3, appliqués aux polynômes de logarithmes premiers ; ils ne reposent pas sur un oracle flottant.

## Jacobi et reconstruction pondérée complète

`jacobi_checks.py` / `jacobi.json` utilisent q = 3,7,11,13,17,19, tous premiers et premiers à N. Tous leurs caractères non principaux sont représentés exactement par des phases réduites modulo les polynômes cyclotomiques. Les cas quadratiques et d'ordre 4 modulo 13/17 sont explicités. Avec C = 10403, la somme complète de `χ(N-Cζ)conjχ(Cζ)` vaut −χ(−1). Sans conjχ(C), elle vaut −χ(−C). La reconstruction de toutes ces moyennes vaut **q−2**, exactement le nombre de termes principaux ; aucun gain ne résulte de cette identité.

La formule jointe centrée est contrôlée sur chaque résidu et **44944 préfixes** : chaque offset, chaque pente unitaire et chaque longueur de 0 à 3q. La discrepancy rationnelle vaut au plus 2. Les pentes divisibles par q sont conservées séparément comme résidus constants ; la borne ≤2 ne leur est pas attribuée.

La reconstruction `S_HH = R_q + T0`, `T0 = -sum_(χ nonprincipales)conjχ(-1)*Tχ` est vérifiée avec poids logarithmiques exacts sur **cinq vrais termes du développé HH**, y = W = 2 : le tuple original ζ=1, son cisaillement j=−78, les deux points ζ=43063/44701 de round6 et la fibre mince ζ=244769,x=43. Les quatre vrais signes μ(u)μ(v)μ(s)μ(t), les unités N, les deux carrés-libres et tous les caps stricts sont conservés. Tous les facteurs de caractères, notamment x et ζ, restent présents.

R_q contient les sites où q|n ou q|m. Le tuple original positif n = 273,m = 99999727 a χ13(n)=0 ; son coefficient ne disparaît pas, mais passe dans R13. Les sommes Jacobi complètes non pondérées ne sont jamais substituées aux poids de ces termes. Le secteur ancien q = 5|N, où le produit est constant χ(−1), reste distinct.

Le diagnostic q = 11,A = 273,C = 10403,e = 3 conserve les **12 cellules CRT** sur ζ=1..9612. Le CRT général importé et figé emploie L=lcm(d²,f), M=lcm(A,e²,ell), puis teste gcd(C L,M)|N avant inversion. Ces cellules de l'expansion signée ne sont pas présentées comme points HH carrés-libres : leurs twists comprennent 0,+1,−1 et les exceptions unitaires restent visibles. Le secteur ζ=1 et le +1 des comptages ne sont pas supprimés.

## Raccord au vrai rang centré

`trace_checks.py` / `trace.json` vérifient la formule native sur 64 résidus non nuls pour les six premiers du banc : `1_(p|m)-1/(p-1) = sum_(χ nonprincipales)χ(n)conjχ(N)/(p-1)`, sous p∤nN. Son facteur est **conjχ(N)** ; le nouveau twist utilise conjχ(m). Ils ne sont pas interchangeables.

Le vrai tuple HH de la fibre mince peut prendre k = 7,s = 3,t = 71,ζ = 34967, avec n = 47864203 et m = 52135797. Les masques originaux restent vrais. Pour q = 7|k, tous les nouveaux twists sont nuls et R7 porte tout son poids ; le rang centré natif vaut pourtant **5/6**. Sur le tuple original, q = 3,7 divisant a et q = 7951,12577 divisant r rendent également tous les nouveaux twists nuls. Pour ces derniers grands premiers, le résultat est certifié par les facteurs exacts, sans énumérer leurs caractères.

La trace ancienne `μ(q)P_q(m)/φ(q) = 1/φ(q)` est contrôlée sur 7394 couples : q∈{1,3,7,11,21,33,77,101,143}, m=1..1024, gcd(q,m)=1. Le support carré-libre de q est conservé : q=9,m=1 donne 0 au lieu de 1/6. Ce contrôle algébrique n'est pas un nouveau théorème de trace ni une borne signée.

## Conservation et hashes finaux

Le registre porte sur **190 anciens artefacts** de round6 et avant : sources, scripts, reçus et builders. Tous leurs SHA-256 restent identiques. REPORT.md vivant, .arbor, caches et round7 sont explicitement exclus. Les scripts ont pris environ une seconde chacun dans cette exécution locale ; ce coût est celui des domaines déclarés, pas d'un calcul complet à N.

| Fichier round7 | SHA-256 |
|---|---|
| logarithmic_checks.py | eb122b2c44e52a053c38d09ad6e3b7c3abe2167bed2c6c23fbc78b62baba789a |
| logarithmic.json | 00f7d0faf027e3b8f31844e4af9042cc2983eaf34aff91994f85af56dbba40d9 |
| jacobi_checks.py | 145946390471b70630b29e3c43918db4db4ba432021709b50b0e8a0f51bdbc9d |
| jacobi.json | 1874d65c4e3d224e03151719a3ed685b1c2127c6ac763c92f44e812bcee9bb13 |
| trace_checks.py | a45cce7c07868c8d994bc76d82fad9666b08bd6635b2c99312f77ae4d40a36c0 |
| trace.json | 919e2d2ae72eadc6ccf713e42c041c5fbac522024f812682379e842f74f972e2 |
| shared.py | 9abc34276b3cdb01fa86bbcafdd447246a29a165d284e2d047e46ff975f427ff |
| previous_artifacts_sha256.json | 900367574d957bfe8e48341ca532022fc0e742d5a001099e3d402863e467de61 |

Pour le Juge : rejouer les trois scripts dans round7 avec le Python embarqué, puis conservation.py. Aucun ancien fichier n'est réécrit. Aucun domaine fini n'est déclaré exhaustif sur N ; aucun calcul global de D_N ou de tout S_full n'est réalisé.
