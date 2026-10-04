# Agent 6 — boucle 9, reçu numérique

2 octobre 2026. **Vérification finie terminée ; audits analytiques et verdict du Juge en attente.** Les deux contrats nouveaux ont été reçus et testés. Les statuts `PASS_IDENTITY_ONLY` ci-dessous concernent exclusivement des égalités finies à N=100000000. Aucun paiement analytique ni aucune victoire Lean ne sont attribués par ce banc.

Le registre gelé inclut 307 fichiers antérieurs de production, dont les 54 fichiers de round8. Les images PNG et les .olean produits sont enregistrés en plus des sources, scripts et reçus. round9, caches de dépendances, .arbor, .git et REPORT.md vivant sont exclus. Conservation initiale : PRESERVED. SHA-256 du registre : `4a637dc44cd1fe2d7ae5850b4999ab052c069084143d69aa52484f66e250fe0f`.

Les helpers9 chargent les anciennes bibliothèques par chemins explicites, sans écriture de bytecode. Aucun ancien banc passé n'a été relancé. Les scripts nouveaux acceptent `--output-dir` et limitent leurs écritures à round9.

Les nouveaux contrats portent sur la face a9=ceil(N^(7/16))=3163 avec Q fixé, et sur le Gram du coefficient réel du bracket long avec deux fronts alpha=100 et H=1000. N=100000000 ne teste que des identités finies. L'onset source est u>=10^24; le seuil BV supplémentaire reste non évalué.

Un échec de contrat a été identifié avant compilation : la première expression de P_bande utilisait Lambda ordinaire et omettait l'unité de k. Le point n=2,m=N−2,r=161,k=621118 passe ses conditions écrites et ajoute log2*log161, tandis que Lambda_N(2)=0. L'idéateur a reconnu l'erreur et fourni V2 avec Lambda_N explicite, ou avec gcd(k,N)=1 ajouté. Ce rejet V1 sera conservé dans le reçu; il ne modifie aucun acquis.

La confusion m=311 a également été corrigée : N−311=113*199*4447 est composite; le raw peut être actif, mais Lambda_N y est nul. Le témoin modèle-seul utile est m=323=17*19, N−m=99999677 premier. Les puissances premières propres du premier axe restent présentes, notamment n=9967^2 et n=9949^2.

## Nouvelle face : V1 rejetée, V2 vérifiée

`new_contract_checks.py` / `new_contracts.json` vérifient, avec Q=999999 fixé, alpha=100 et a9=3163, l'égalité pointwise

`S_Lambda^alpha − S_Lambda^a9 = −P_bande_V2 − Z_face`.

Les deux expressions corrigées de P_bande sont comparées indépendamment : Lambda_N et gcd(k,r)=1, ou Lambda ordinaire avec les deux conditions gcd(k,N)=1 et gcd(r,kN)=1. Les faces alpha<r<=a9 et alpha*k<m, a9*k<m restent littérales. Les puissances entières certifient ceil(N^(7/16))=3163 et floor(N^(3/8))=1000.

Domaines déclarés : m=1..1024 pour une tête, puis les 12 points 173,303,311,323,2121,3183,9507,32421,112211,658911,1017399,N−2. La queue m>1024 n'est pas énumérée. Les colonnes ALL-k et k>=2 sont conservées séparément; leur différence k=1 se compense conjointement entre P_bande et Z_face.

À m=2121, n=99997879 est premier, P_bande ALL-k=0, mais P_bande k>=2=log(n)log2121. Ce point n'est donc pas un modèle-seul après retrait de k=1. Le proprepower n=9949^2, m=1017399=3*17*19949, donne au contraire P_bande=0 pour les deux versions et un Z_face non nul. Lambda_N=log9949 y demeure présent malgré mu(n)^2=0.

La version V1 avec Lambda ordinaire et sans unité de k reçoit `ERROR_FALSIFIER`, avec le tuple n=2,r=161,k=621118 et son excès exact log2*log161. V2 reçoit `PASS_IDENTITY_ONLY_CORRECTED_V2`. Le rejet V1 n'est pas effacé par la correction.

## Ligne k=3 : deux signes réels après relèvement

Sur m>3a9, les deux expressions de la nouvelle ligne k=3 sont comparées : coefficient direct avec les deux détecteurs, et partition native en résidus modulo 3. Les témoins utilisent exactement le même a9, Q et Lambda_N :

* m=32421=3*101*107, n=99967579 premier, mu(m)=−1 : E3=+(1/2)log99967579*log10807>0;
* m=9507=3*3169, n=99990493 premier, mu(m)=+1 : E3=−(1/2)log99990493*log3169<0.

Les signes sont certifiés par intervalles rationnels de logarithmes, sans flottants. Le candidat m=31209 ne fournit aucune contribution Lambda_N : n=13*419*18353 est composite. Ces points réfutent une faveur pointwise générale de la ligne; ils ne réfutent aucune compensation globale.

## Opérateur pondéré réel : identité seulement

Pour les cinq points m={303,311,323,658911,112211} et J={3,7,11,13}, le banc conserve

`a_k=log(m/k)[1_(k|m,H*k<m) − 1_(alpha*k<m,gcd(k,nN)=1)/phi(k)]`

et `w_m=Lambda_N(N−m)mu(m)^2`, sans masque carré-libre sur n. Il compare la contraction des vraies valeurs mu(k) de Gamma avec la somme physique des carrés; vérifie séparément DD−DM−MD+MM; et vérifie que le premier moment s'écrit aussi sum w_m*mu(m)*sum mu(k)a_k. Les diagonales ne sont pas retirées. Statut : `PASS_IDENTITY_ONLY_WEIGHTED_ENERGY`.

À m=323, la colonne k=3 est réellement modèle-seul : 300<323<=3000, n premier, a3=−(1/2)log(323/3); la diagonale log(n)*a3^2 est strictement positive. Le premier axe n=9967^2, m=658911=3*11*41*487, garde Lambda_N=log9967 et mu(m)=+1. À m=112211=11*101^2, le poids est nul par mu(m)^2, tandis que n=99887789 est premier. Cette origine du masque sur m est distincte d'un masque illégitime sur n ou sur une tête coupée.

La ligne native q=3,k=3,m=658911 est physique active et garde n mod3=N mod3=1 : son quotient de caractères vaut exactement 1. Cette phase ne devient pas une oscillation. Les tests portent le bracket entier réindexé et ne revendiquent aucune diagonalisation des quatre Möbius d'une cellule HH ni un transfert du Gram nu aux coefficients HH.

La nouvelle preuve écrite du paiement des properpowers proposée par l'Agent 2 relève de l'audit mathématique, avec son seuil déclaré u>=65536 et le seuil source u>=10^24. Le JSON marque explicitement `properpower_analytic_payment_tested=false`. Aucun budget de cette preuve n'est évalué ni validé à N=10^8.

## Conservation et rejeu isolé

Le registre9 couvre les 307 fichiers antérieurs et reste inchangé avant et après les tests. Une lecture indépendante des 227 entrées de l'ancien registre8 confirme aussi leurs empreintes actuelles; aucun ancien banc n'a été exécuté pour cette vérification de conservation.

Le rejeu neuf avec `--output-dir round9/isolated_output_probe` produit exactement les mêmes octets que le reçu canonique. Le chemin de sortie n'est pas incorporé au JSON. Les bibliothèques historiques sont chargées par chemins vérifiés et leurs SHA sont consignés. Le script ne crée aucun bytecode ancien et n'appelle pas Lean.

| Fichier round9 | SHA-256 |
|---|---|
| new_contract_checks.py | e0b8fb5a56757b7773d8be30365d78af36aa7ab7aa6b999735923dfc0bc79b1c |
| new_contracts.json | ac5bad36c2527886c6f3ac10150aa44c8f20550d683ef5a0eedab5160a60271d |
| shared.py | ee0ec92266a9a4c76e6df2a346a65bc28e4fc2a1cb4718b2bb6e1ebb09889694 |
| conservation.py | 38ca5bab121ddf0d9b1eced2cee3a31d49973140f8f2c26a98642b37572124ff |
| previous_artifacts_sha256.json | 4a637dc44cd1fe2d7ae5850b4999ab052c069084143d69aa52484f66e250fe0f |

Les nombres de points ci-dessus décrivent les domaines distincts du reçu final; les relectures de développement ne sont pas additionnées comme des preuves indépendantes. Aucun calcul global de D_N n'a été effectué et aucun nouveau certificat Lean n'est revendiqué.
