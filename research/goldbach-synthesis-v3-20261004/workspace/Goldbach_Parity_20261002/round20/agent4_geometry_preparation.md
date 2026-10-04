# ROUND20 — préparation source de la géométrie de 14.5

Statut : **source Lean et lanceur préparés, aucune invocation Lean, aucun calcul Python mathématique, aucun PASS, aucun score, aucune victoire**. Écritures limitées à `round20/role4_geometry/**` et au présent rapport. Les feedback01/02/03, FINAL2, les sept PASS de ROLE4, Demand et l’agrégation F2 sont intacts. Ce travail formalise les arrondis de l’hypothèse 14.5 déjà sélectionnée ; aucune nouvelle hypothèse ou sélection n’a été introduite.

Le skill executor a été lu intégralement (`71090b`, SHA `54f445fb2591b649420013c872e70dc009af42de38162b63e0e76239b8880337`). L’attribution explicite du coordinateur impose le répertoire séparé et l’interdiction de compiler avant sa lecture FULL et sa gate propre. Elle prime sur le workflow générique worktree/évaluation du skill. Aucune permission supplémentaire n’a été demandée.

## Définitions et entrées

[FINAL2](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/agent2_friable.md) a été relu **FULL** dans `d0db51`, SHA `5635cff82cbd5e6e395dfef3617f8d2d89ead40f6dbbdfffa943bf0f6a785be5`. Le texte extrait de la monographie est resté inchangé (SHA `ded7e6252ed3b620537fc471d11778fe16abd1305ec4c6959fa185546a5be687`) ; ses passages de géométrie ont été recherchés/lus, sans nouvelle extraction ou exécution. Le PDF fixé porte le SHA déjà enregistré `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24`.

[FriableSourceGeometry.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/FriableSourceGeometry.lean:19), namespace `GoldbachRound20.Friable.SourceGeometry`, définit réellement :

```text
u=log N, ell=log u, T=u/(128 ell), Y=Nat.floor(exp T), sigma=(log Y)^(-1)
D=Nat.ceil(sqrt N), M=Nat.ceil(N^(3/4)), a=Nat.ceil(N^(7/16))
alpha=Nat.ceil(N^(1/4)), Z=Nat.floor(N^(1/4)), Q=(N-1)/alpha
Ecap=(N-Q-1)/M, Eupper=N/M
SourceOnset N := (10:Real)^(24:Nat) <= log N
```

`Ecap` garde le cap de FINAL2. `Eupper` est son agrandissement positif pour F2. `source_Q_floor` et `source_Ecap_floor` écrivent l’égalité avec les floors de quotients **réels**, après justification des soustractions naturelles. Aucune division naturelle n’est remplacée par un quotient réel exact. La source démontre séparément `M<=N`, `0<Eupper` et `Ecap<=Eupper`; la positivité inconditionnelle de `Ecap` n’est pas une garde requise ou annoncée.

SHA de la source proposée : `22bb640570931e2d7ad2575347d6b5099270dda4680e3d7472939d4f20449d13`. Contrôle textuel uniquement : 62 directives `#print axioms`, zéro `sorry`, `admit`, `native_decide`, `trustMe`, zéro déclaration `axiom`. **Les directives n’ont pas été exécutées** : aucune liste d’axiomes du nouveau module n’est encore certifiée.

## Gardes effectivement visées par les preuves écrites

Les gardes sont conclues à partir de `SourceOnset`, puis réunies dans [source_geometry](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/FriableSourceGeometry.lean:374). La structure `SourceGuards` n’est pas une entrée libre du wrapper.

| Garde | Théorème de la source |
|---|---|
| `0<u`, `1<=u`, `6<=ell` | `source_u_pos`, `source_u_one`, `source_ell_six` |
| `8<=T`, `T<=u/128`, `0<Y` | `source_T_eight`, `source_T_le_u_div_128`, `source_Y_pos` |
| `4<=log Y` | `source_logY_four` |
| `1+log Y<=u` | `source_one_add_logY_le_u` |
| `128*log u*log Y<=u` | `source_scale` |
| `0<sigma<=1/4` | `source_sigma_pos`, `source_sigma_le_quarter` |
| `u/2<=log D`, `3u/4<=log M` | `source_D_log`, `source_M_log` |
| `1<D<=M`, `0<M<=N` | `source_D_gt_one`, `source_D_le_M`, `source_M_pos`, `source_M_le_N` |
| `0<alpha<=a`, `1<=a<M` | `source_alpha_pos`, `source_alpha_le_a`, `source_a_one`, `source_a_lt_M` |
| `Ecap<=Eupper<=a`, `Eupper<=N^(1/4)` | `source_Ecap_le_Eupper`, `source_Eupper_le_a`, `source_Eupper_le_quarter_power` |
| `D<=2sqrt N`, `Y<=N^(1/128)<=N^(1/4)`, `Y<=Z` | `source_D_le_two_sqrt`, `source_Y_le_small_power`, `source_Y_le_Z` |
| `H_e<=u/2` pour `e<=Eupper` | `source_rank_harmonic_le_half_u` |

La chaîne papier suivie par le code est élémentaire et effective. `exp 1<3` donne `exp 6<=3^6<=u`, donc `ell>=6`. L’API `Real.log_le_rpow_div` avec exposant 1/2 donne **`ell<=2sqrt u`**, une borne dérivée légèrement plus faible que l’exemple papier de FINAL2, suffisante au même seuil. Comme `sqrt u>=2048`, on a `1024ell<=2048sqrt u<=u`, donc `T>=8`. `Nat.div_two_lt_floor` donne `exp T/2<Y`; ainsi `log Y>=T-log 2>=7>=4`. Le floor supérieur donne `log Y<=T`; `ell>=6` donne `T<=u/128`, puis `1+log Y<=u`. La garde d’échelle suit en multipliant par `128ell>0`.

Les ceils donnent `D>=sqrt N`, `M>=N^(3/4)` et leurs bornes logarithmiques. La monotonie des puissances et des ceils donne `D<=M` et `alpha<=a`. Pour le front strict, `N^(5/16)>=2`, `N^(7/16)>=1` et `N^(3/4)=N^(7/16)*N^(5/16)` donnent `N^(7/16)+1<=N^(3/4)`; `ceil x<x+1` conclut `a<M` avec les arrondis réels. Enfin `Nat.cast_div_le` et `M>=N^(3/4)` donnent `Eupper<=N^(1/4)`, puis `Eupper<=a`. La borne harmonique traite `e=0` séparément et utilise `log e<=u/4` lorsque `e>0`.

[actual_source_cap_rank](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/FriableSourceGeometry.lean:328) emploie le vrai `StructuralSupport` et son cap `e*q+Q+1<=N`, puis `q>=M`, pour conclure `e<=Ecap`. `actual_source_cofactor_guards` conclut alors `e<=a` et `a<q`. Les gardes de squarefreeness, unités, primalité de q, sélecteur et ressources demeurent celles du vrai support ; elles ne sont pas inférées du seuil.

## Interfaces et provenance de lecture

ROLE4 a confirmé les interfaces par messages de coordination. La source importe uniquement mathlib et les nouveaux PASS `FriablePrimeHarmonic`/`FriablePhysicalPayment`, en lecture seule. Elle n’importe pas Demand ou l’agrégation F2 encore en cours. Le manifeste [inputs_sha256.json](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/inputs_sha256.json) lie FINAL2, les sources/oleans des six PASS transitifs, les dépendances historiques auditées, le skill et les fichiers API locaux. Les hashes des imports ont été réellement vérifiés contre le ledger ROLE4 (`077931`, exit0); le ledger mutable lui-même n’est pas une dépendance gelée du lanceur.

Lectures API ciblées sur mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`, sans compiler : `Floor.lean` (`91a29f`, `cdb7d5`, `7cb789`), `Pow/Real.lean` (`a431df`, `c60ed3`, `42ce11`, `888156`), `Real/Sqrt.lean` (`abef5f`, `7cb789`), `Log/Basic.lean` (`854bec`, `92718c`), `Complex/Exponential*.lean` (`abef5f`, `888156`), casts/division/harmoniques (`3c88b2`, `7cb789`), et `Init/Data/Nat/Basic.lean`/`Lemmas.lean` (`e07cdb`, `d5c036`). Quelques recherches ont signalé un chemin absent, un wildcard Windows invalide ou un ancien répertoire sans accès ; ce sont des incidents de lecture shell, **aucun échec Lean ou numérique**.

Les wrappers [de fin de source](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/FriableSourceGeometry.lean:384) n’ont que `SourceOnset` comme prémisse de taille et visent : la vraie masse du band `<=u^-37`, la vraie somme friable pondérée par `tau(n)=card(n.divisors)` `<=N*u^-42`, et le vrai coût réciproque F1 unique `<=7N*u^-39`. Aucun petit `S_D`, agrégat cible, totient envelope libre ou capacité n’est pris comme prémisse.

## Gate et obligations non fermées

[compile_once.py](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/compile_once.py), SHA `0745f9c34c49e930422d4505aeac474e1812ceb6a9121aede2b2acea7681f0a1`, est **préparé et jamais exécuté**. Il demande une gate distincte `ROOT20_GEOMETRY_COMPILE`, les lectures FULL source/lanceur/préparation, leurs hashes et celui du rapport, ainsi que le contrôle numérique canonique déjà inspecté par root. Son unique cible future est le nouveau module de géométrie. Il enregistre snapshots PREEXEC, début/fin, exit réel, stdout/stderr/log et olean; il interdit le rejeu du PASS inchangé. Aucun ancien producteur ou source historique n’est une cible.

Le contrôle statique ne remplace pas le compilateur : élaboration des casts, dépliage des définitions, choix implicites des exposants et fermeture tactique restent **non vérifiés** jusqu’à une tentative autorisée réelle. Il n’existe actuellement aucun log/receipt de compilation de géométrie et aucun `.olean` de ce module.

F2 total et son raccord quantitatif restent confiés à ROLE4. Les bornes écrites ici fournissent `H_Eupper<=u/2`, `Eupper<=N^(1/4)`, `D<=2sqrt N`, `Y<=N^(1/128)` pour conserver tous les fronts `+1`; sous la future agrégation réelle, elles donneront les termes papier `7N/u^33+28N^(97/128)/u^34`. F4 et l’union exacte des coûts ne sont pas prouvés dans ce paquet. `e<=Q` et la positivité inconditionnelle de `Ecap`, non consommés par les interfaces locales, ne sont pas annoncés comme nouveaux théorèmes ici.

Le bridge vers le support source entier, les réciproques m1 non friables de `F0\F1`, le complément où les deux ressources ont un grand facteur, les singletons/e1/p0, Gamma/T_A, les autres faces/nonbulk et la capacité du ledger entier restent ouverts. Aucun wrapper géométrique, même compilé, ne constitue la victoire demandée.
