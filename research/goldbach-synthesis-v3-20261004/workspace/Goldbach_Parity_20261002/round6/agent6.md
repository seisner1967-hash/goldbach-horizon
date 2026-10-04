# Agent 6 — reçu numérique final, boucle 6

2 octobre 2026. **N = 100 000 000** dans tous les bancs. PASS désigne les identités finies corrigées et les falsificateurs vérifiés ; aucune prétention de gain analytique ni borne sur D_N n'est validée.

## Profil réel et dilatations

`katai_checks.py` / `katai.json` vérifient symboliquement `a*S = -sum mu(m)*B(m) + R`, la normalisation par les planchers et la formule de Gram avec ses diagonales et exclusions p∤m. Domaines : X = 512, 1024 avec P = {3,7,11,13} ; X = 303, 1024 avec P = {2,5}. Les profils F_N(pm), les faces strictes et les unités sont calculés à leurs véritables arguments. Aucune petite corrélation n'est supposée.

Pour X = 303, P = {2,5}, `a = 211/303`, `B = G = 0`,

`S303 = -1/2 log(99999697) log(101) ≠ 0`, `R = (211/303)*S303`.

Seul m = 303 est actif dans ce préfixe. Les monômes (7,101), (41,101), (101,348431) ont coefficient −1/2 dans S et −211/606 dans R. L'extérieur de **99 999 696 arguments** demeure non calculé. Le transfert oubliant le résidu de couverture est falsifié ; l'identité Kátai ne l'est pas.

Le profil brut conserve rho1 sans masque μ(n)². Le témoin actif `n = 9967² = 99341089`, `m = 658911 = 3*11*41*487` a μ(m) = 1, μ(n)² = 0, `fII(n) = -log9967` et F_N(m) strictement positif ; son préfixe strict est 6589. Le témoin m = 311 est aussi positif avec porteur HH nul. Inversement, le vrai tuple HH (a,b,r,k) = (21,13,99999727,1) a porteur 4 et couverture nulle par {3,7,11,13}. Les deux profils ne sont pas assimilés.

Les monômes logarithmiques ont des coefficients rationnels. Les signes sont encadrés par les intervalles artanh de `round3/multifibre_checks.py` : réduction à x∈[1,2), reste géométrique majoré, puis intervalle de chaque monôme. Aucun logarithme flottant n'est utilisé comme oracle.

## Deux carrés, CRT et caractères

`squarefree_checks.py` / `squarefree.json` vérifient **1066 cas finis**, 23544 cellules signées brutes et **558 cellules CRT compatibles**. Domaines exacts : A = 273, C = 10403, ζ = 1..512 ; A = 273, C = 187, ζ = 40000..45000 avec A|(N−Cζ) ; le point original ζ = 1 ; une fibre mince. Chaque domaine est testé avec W = 2 et 19. Les coefficients d'inclusion-exclusion restent présents avant regroupement. L'omission de f partageant 5 ne vaut que dans l'identité tordue où χ5(ζ) = 0, jamais dans une identité non tordue après cette omission.

Le S3 initial est incomplet. A = 273, C = 10403, d = ell = 11, e = f = 1 satisfont ses exclusions écrites, mais M = 3003 et gcd(C f d²,M) = 11 ne divise pas N : cellule vide, inverse non tenté. Le second témoin C = 187, d = ell = 19 donne M = 5187 et gcd = 19. Le script général utilise `L = lcm(d²,f)`, `M = lcm(A,e²,ell)`, teste `gcd(C L,M)|N`, puis réduit avant inversion. Dans S3 corrigé, gcd(d,f) = 1 donne L = f d² ; gcd(d,ell) = 1 et gcd(C,N) = 1 sont explicites. Un cas d = f = 3 hors S3 confirme L = 9 au lieu du produit erroné 27.

Quand e = 3 partage A = 273, M = 819 donne exactement 12 points dans 1≤ζ≤9612 ; le module produit 2457 n'en conserverait que 4. Ce sont des cellules signées de l'expansion, pas des points HH carrés-libres. Les cellules compatibles d = e = 2 sont également conservées avec poids physique nul par les unités.

La fenêtre ζ = 40000..45000 contient 19 points dans la congruence de pas A, dont **2** gardent les masques HH originaux y = W = 2 : ζ = 43063 et 44701. Leur caractère isolé varie ; le produit complet `χ5(A)χ5(x)conjχ5(C)conjχ5(ζ)` est constamment +1 pour le caractère quadratique, −1 pour l'ordre 4. Valeurs et conjugaisons sont des entiers de Gauss exacts. Les périodes isolées de 5, ou de 10 avec le masque unité N, sont testées séparément et ne remplacent pas le produit constant.

Le point original ζ = x = 1, A = 273, C = 99999727 reste présent. La fibre A = 1113121, C = 213 possède ζ = 244769, x = 43. Son intervalle brut 1..464257 dépasse sqrt(N), mais n'admet qu'un point dans la congruence de pas A ; N/(AC) = 100000000/237094773 < 1. Le +1 du comptage est indispensable.

## Conservation et SHA-256 finaux

Les **160** anciennes sources, scripts, reçus et builders inventoriés sont inchangés ; les caches et fichiers centraux vivants sont explicitement exclus. Les nouveaux scripts restent dans round6. Le Juge peut rejouer les deux bancs, puis `conservation.py`, avec le Python embarqué.

| Fichier round6 | SHA-256 |
|---|---|
| katai_checks.py | baa5f38424d501a5114409257488ac05a6c10a5a3cba7b35b89ddd63accfebb0 |
| katai.json | 43d7f7a33d3b412ed8eaabd995902c1eeb71555aba9b8951226966631d1b6b96 |
| squarefree_checks.py | 150a78a5477168314f946de6dab26e3129552546c544bad07326f3763471d7e5 |
| squarefree.json | 053a237abec6a36d4f5ec28bd2dcb652f63f09a9c789986522cb77d528a71a7b |
| exact_tools.py | f48bb0b2b608aa734944cbfe978c19ad55f5aa249068dcc313a1de6da5a393cc |
| conservation.py | 5c435fa7c0886604a6e51c3df36015bf4c2219c562d964cb5fd69968323d92db |
| previous_artifacts_sha256.json | bff50b025ed0ca2f072739edcfc04e91c94acd8f7d9cff24b27c53a2f5928684 |

Les reçus sont ceux des versions finales comprenant X = 303, la puissance première active et les corrections CRT. Aucun échantillon n'est déclaré exhaustif sur N. Aucun calcul global de S_full, du moment HH signé ou de D_N n'est effectué.
