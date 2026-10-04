# Agent 6 — boucle 10 : TERMINÉ

**TERMINÉ — nouveaux contrats finis vérifiés, entrées numériques gelées pour le Juge.** Les résultats sont PASS_IDENTITY_ONLY. Les extensions fausses sont ERROR_FALSIFIER; aucun de ces échecs arithmétiques n'est décrit comme un échec du compilateur. Aucun signe asymptotique, paiement analytique ou gain global sur D_N n'est validé par N=100000000.

Le registre10 protège 341 fichiers jusqu'à la boucle9 terminée, dont ses 34 fichiers, tous les PNG et les .olean produits. SHA-256 du registre : `39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb`. Conservation avant et après les nouveaux bancs : PRESERVED. Les répertoires roundNN avec NN>=10 sont exclus par numéro explicitement parsé; les additions dans les anciennes boucles restent détectées. Caches, .arbor, .git et REPORT.md vivant sont exclus. Le helper9 gelé n'a pas été modifié ni exécuté après création de round10.

Les SHA originaux du PDF et du ZIP sont vérifiés contre INPUT_HASHES.json : PDF `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24`, ZIP `32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd`. Le controller9 final attendu est `ef316624b2c49ee3689de9ce24cbf9ecb531fc05e913760341118c47afc334d3`.

Les nouveaux scripts utilisent des bibliothèques historiques chargées par chemins explicitement vérifiés, sans écriture de bytecode. Ils acceptent --output-dir. Le rejeu dans round10/isolated_output_probe produit exactement les mêmes champs et les mêmes octets pour les deux JSON; le chemin de sortie n'entre pas dans les données. Aucun ancien banc passé n'a été relancé.

N=100000000 reste un banc fini. Les paiements écrits harmoniques et properpower restent hors validation numérique à ce N; seuil source u>=10^24, seuil BV supplémentaire non évalué. Un échec de formule reçoit son propre falsificateur arithmétique; il ne sera jamais présenté comme un échec du compilateur Lean. Aucun calcul global de D_N ni aucun nouveau Lean n'est revendiqué.

## Domaine et conventions

`witness_search.py` sélectionne des points selon des domaines finis consignés, puis factorise réellement m et n=N−m. `paired_cofactor_checks.py` teste les identités nouvelles sur 11 points distincts dont n est effectivement premier et unitaire. Les puissances entières certifient a9=3163, a9^3>N et Q(a9+1)>N−1. Q=999999 reste original.

`W_kernel` est le W source avec log(k/m); `W_positive=−W_kernel` est la convention de l'Agent 2. Le coefficient apparié est C_m=−mu(m)[D_a9(m)−W_kernel(N−m,m)]. Les deux fronts sont strictement a9*k<m. Le modèle ENTIER est calculé pour chaque k<=min(Q,floor((m−1)/a9)), avec gcd(k,nN)=1. Les versions ALL-k et k>=2 sont calculées séparément et coïncident par annulation conjointe de k=1. Aucun masque mu(n)^2 n'est introduit dans le raw original.

## U1, fibre courte et partition j=0,1,2

Le banc compare indépendamment −mu(m)D_a9(m), mu(m)^2*sum_(r|m,r>a9)mu(r)log r, et mu(m)^2[−Lambda(m)−sum_(r|m,r<=a9)mu(r)log r]. U2, qui complète la fibre courte en c, est appliqué seulement à j=2 avec c<=floor((N−2)/(a9+1)^2)<a9.

Les témoins bulk ont m>=10^6 et n>Q :

| m | n premier | Structure | Signe de C |
|---|---|---|---|
| 1000037 | 98999963 | m premier rough | négatif |
| 10036223 | 89963777 | 3167*3169 | négatif |
| 30108669 | 69891331 | 3*3167*3169 | positif |
| 10526181 | 89473819 | 3183*3307, j=1, c>a9 | positif |
| 1174173 | 98825827 | 3*7*11*13*17*23, j=0 | positif |
| 30089667 | 69910333 | 3*3167^2 | zéro |

À c=3183=3*1061, U_a9(c)=−log3−log1061, alors que −Lambda(c)=0. Remplacer cette fibre incomplète par la complète est ERROR_FALSIFIER; U1 donne correctement L=log3183. En j=0, L vaut 5log3+5log7+3log11+3log13+4log17+3log23 et reste entier.

En j=2,c=3, C=log3−W_kernel>0 : « tout J2 favorable » reçoit ERROR_FALSIFIER. Les contributions rough négatives restent présentes. La phase native q=3,k=3 du nouveau point m=30108669 vaut 1, car n mod3=N mod3=1; aucun gain d'oscillation n'en est déduit. Les anciens quatre Möbius HH et leurs modules ne sont pas diagonalises par ce banc.

Les certificats de logarithmes utilisent les bornes artanh rationnelles historiques, arrondies vers l'extérieur sur une même grille dyadique. Ils consignent leurs bornes, termes et bits. Des assertions strictes exigent les deux signes rough négatifs, le c=3 positif et les zéros non carrés-libres : UNRESOLVED ne peut pas conserver un statut de falsification. Une recherche initiale m=p^2 rough était vide pour une raison structurelle : N mod3=1 et p!=3 donnent n mod3=0. Ce diagnostic n'est ni une formule fausse ni un échec Lean.

## E3 : un grand premier, petit cofacteur

Pour m=p*c, 1<=c<=min(a9,Q)<p, le banc vérifie C_m=mu(c)[W_positive(N−pc,pc)−Lambda(c)−1_(c=1)log p]. Les cinq cas sont c=1,p=1000037; c=7,p=3167; c=21,p=3169; c=231,p=3191; c=9,p=3181. Les n respectifs 98999963,99977831,99933451,99262879,99971371 sont vérifiés premiers. Les C sont négatif, négatif, positif, négatif, zéro.

Pour c=9, T nu=Lambda(9)=log3 mais mu(pc)=0 et le bracket entier est nul. L'extension omettant mu(m)^2 reçoit ERROR_FALSIFIER : le défaut n'est pas nécessairement l'identité du T nu. Les extrapolations de T=Lambda(c) sont aussi réfutées pour c>a9 sur m=3167*3169 et pour p<=a9 sur m=3*23,n=99999931 premier. E3 corrigée reçoit PASS_IDENTITY_ONLY.

## E6 : ratio singulier, petits n et multiplicité

Pour les n premiers unitaires des témoins, plus n=3, le banc vérifie exactement S(nN)/S(N)=1+1/(n−2) par les facteurs finis. La constante commune C2 est factorisée, sans approximation de son produit infini. La correction normalisée sum_(n distincts)log(n)/(n−2) est comparée aux mêmes termes issus du ratio. Le petit n=3 est conservé avec coefficient 1.

Les extensions n=5 non unitaire (ratio réel 1) et n=9 properpower (ratio réel 2) sont ERROR_FALSIFIER. Pour m=22169, les représentations (3167,7) et (7,3167) partagent le même n, mais seule la première est canonique pour E3. Les compter toutes deux double abusivement log(n)/(n−2). Ce défaut est consigné sans multiplier la somme distincte par un nombre de p. Le paiement analytique polynomial de cette correction est hors validation numérique.

## Empreintes gelées et portée

Le JSON canonique paired_cofactors.json contient 395236 octets; witnesses.json contient 8839 octets. Les champs et octets du rejeu isolé sont identiques. Les bibliothèques historiques et leurs SHA sont consignés dans les reçus.

| Artefact round10 | SHA-256 |
|---|---|
| paired_cofactor_checks.py | bdee7952e47419fef2a0512d8e74a7234bf3da6800e2dc9561b94f9bd34d5ef2 |
| paired_cofactors.json | 909df1b5cd38a4ed42cad65ca8930c47930d7ba8afd356148d87f4c7edcf34b2 |
| witness_search.py | 3ac3774c25997c8a59c13862ada7b843bb19f7dd178bba0b45d0d5be5ddd28bb |
| witnesses.json | 527df6b3bc8a71cdbf6e76b428b048d13c8cf6af764f94d0fb7b94a5f008d598 |
| shared.py | 1c49e5abc36ceacfd65e8fc7ca97cee1705a60e693870b6e4942091ba2a1d868 |
| conservation.py | 6b27a617019d937fd4c40d243b0173240984d126ecd377d15cbf2b9934cc7254 |
| previous_artifacts_sha256.json | 39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb |

Statut final : PASS_FINITE_IDENTITIES_ONLY, avec falsificateurs limités aux extensions exactes désignées. Ce rôle n'appelle pas Lean; les audits des formalistes et le verdict du Juge sont distincts. Aucun paiement écrit indépendant n'est crédité par ces échantillons, aucun moment D_N global n'est calculé et aucune victoire sémantique n'est revendiquée.
