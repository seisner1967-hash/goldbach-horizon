# FINAL20 — géométrie source auxiliaire compilée

**PASS Lean4.15 réel de `FriableSourceGeometry.lean`, tentative02, sous la gate distincte root.** Exit0, crédit PASS accordé, intégrité après exécution complète : 104 contrôles inchangés. Les 62 `#print axioms` n’affichent que `propext`, `Classical.choice`, `Quot.sound`, sans `sorryAx`. Ce résultat ferme les gardes géométriques de la piste14.5 au seuil original ; il ne constitue pas la victoire Goldbach/parité.

La source PASS [FriableSourceGeometry.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/FriableSourceGeometry.lean) est gelée, SHA `bc249b736e460716cccc7e8a9f9ccab9ac508133c8664bd6278795bd3dcb890a`. L’olean publié au même répertoire porte le SHA `a18d92c97badf4ddb7ebff9c96b1367114c3748b99d7dc09558e4bfd565044b3`. Son unique différence avec la première source relue `22bb640…` est la fermeture explicite de `(2:Real)-1=1` par `calc`/`norm_num`, après un véritable FAIL.

## Ce qui est maintenant prouvé

Namespace : `GoldbachRound20.Friable.SourceGeometry`. Les paramètres sont les vrais floors/ceils de FINAL2 : `u=log N`, `ell=log u`, `T=u/(128ell)`, `Y=floor(exp T)`, `D=ceil sqrt N`, `M=ceil N^(3/4)`, `a=ceil N^(7/16)`, `alpha=ceil N^(1/4)`, `Z=floor N^(1/4)`, `Q=(N-1)/alpha`. `source_Q_floor` prouve l’égalité au floor du quotient réel original ; `source_Ecap_floor` fait de même pour `Ecap=floor((N-Q-1)/M)`. L’agrandissement `Eupper=N/M` est distinct et positif.

Le théorème compilé `source_geometry (h : SourceOnset N)` construit les **25 gardes**, avec pour seule prémisse de taille `SourceOnset N`, littéralement `(10:Real)^(24:Nat)<=log N`. Les gardes ne sont pas prises en hypothèse :

- `0<u`, `1<=u`, `ell>=6`, `Y>0`, `log Y>=4`, `1+log Y<=u`, `128*log u*log Y<=u`.
- `1<D<=M`, `0<M<=N`, `0<Eupper`, `log D>=u/2`, `log M>=3u/4`.
- `0<alpha<=a`, `1<=a<M`, `Ecap<=Eupper<=a`, `Eupper<=N^(1/4)`.
- `D<=2sqrt N`, `Y<=N^(1/128)`, `Y<=Z`, `H_Eupper<=u/2`.

Les théorèmes séparés prouvent également `T>=8`, `T<=u/128`, `0<sigma<=1/4`, et `H_e<=u/2` pour tout `e<=Eupper`. La preuve utilise seulement des inégalités élémentaires mathlib, la monotonie log/rpow et les APIs des arrondis ; aucun onset supplémentaire ou assertion de petite somme n’est ajouté.

Sur le **vrai** `StructuralSupport` importé, `actual_source_cap_rank` prouve `e<=Ecap` à partir de `e*q+Q+1<=N` et `q>=M`. `actual_source_cofactor_guards` conclut `e<=a` et `a<q`. Les propriétés de primalité, squarefreeness, unités et ResourceCell restent exactement celles de ce support.

Trois wrappers compilés consomment les nouveaux PASS ROLE4 en lecture seule et ont uniquement le seuil source pour prémisse de taille :

```text
actual_source_divisor_band_mass : sum_(d in actual divisorBand D Y) 1/d <= u^-37
actual_source_smooth_tau_tail : sum_(M<=n<=N, actual Smooth Y n) tau(n) <= N*u^-42
actual_source_unique_F1_reciprocal : actual uniqueReciprocalCost1 <= 7*N*u^-39
```

`tau` reste la cardinalité des vrais diviseurs ; la réunion F1 consomme l’image physique q une fois. Aucun petit S_D, kernel libre, petit agrégat, capacité ou cible D_N n’apparaît comme prémisse.

## Exécution et provenance

Gate : `round20_source_geometry_authorization.json`, SHA `03c97de5c89feee39a9ad599427e14e4239f75025ba6eb85e375036ab1710549`. Launcher v2 gelé : `ac1b9f2e3426a1ca9c311d3d6481b4a102bed6a3ac125ec404f214b47e58baff`; préparation v2 : `84b028061f37c88457cf75af185250358c387259f629dcc42361007d2430ee61`. Le rapport de préparation initial et les archives v1 n’ont pas été modifiés. Le manifeste des entrées gelées garde le SHA `5d8b757ed6460b34c06ba23014ca95ebf808ee5669a5242e9742823c7e52d997`.

La tentative01 a réellement échoué à la ligne147 : `simpa` conservait `Real.log2<=2-1` au lieu de normaliser le RHS à1. Sa sortie1, son snapshot source, son START, son `finished_raw` et son log sont conservés. `sorryAx` apparaissait sur le théorème raté et ses dépendants, sans crédit. Ce défaut tactique n’est ni une réfutation mathématique ni un obstacle de parité.

La tentative02 compile la source changée, exactement autorisée comme réparation après FAIL. START/FIN en UTC : `2026-10-03 04:02:08.949583` à `04:03:03.232369`. Les receipts originaux portent leur offset `+02:00`, sans réécriture. Le [log02 FULL](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/attempt02.log), relu dans `643632`, SHA `1a79f4d6f234151eb6ecbd86bce261a3d89ea50856647d686602af2500f2de4d`, confirme le PASS et les axiomes standard. START02 SHA `c15542195bb8ec6ee3dfe44027f37ccfce705573226d01e1597bca628c4830af`; `finished_raw`02 SHA `b3ef33b3ca377d47e0c83329b4a95efe22af8a064de556e32eced91738f955f2`.

Ledger final [geometry_build_receipt.json](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/geometry_build_receipt.json), SHA `dee0fca8a69ce57490d70fd36f9bcab149caad91613655581b807d77cec424de` : deux tentatives, un FAIL puis un PASS, un module publié. Source/snapshots, runtimes Lean/Python, gate/lanceur/préparation/rapports/manifeste/archives v1, 47 entrées gelées et 38 liaisons numériques canoniques ont été vérifiés après le subprocess. Aucun ancien source/PASS n’a été ciblé ou rejoué, aucune exécution Python mathématique, aucune invocation du Juge par cet auteur. Les détails d’échec sont dans [geometry_actual_failures.md](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/geometry_actual_failures.md).

## Portée et obligations restantes

Ces gardes raccordent la masse Euler/Rankin et F3 **au vrai seuil et aux vrais paramètres source**. Elles fournissent exactement les majorations `H_Eupper<=u/2`, `Eupper<=N^(1/4)`, `D<=2sqrt N`, `Y<=N^(1/128)` attendues pour l’agrégation F2 et ses fronts. ROLE4 possède la compilation d’agrégation et le futur raccord SourceBudget/F4 ; aucune invocation Budget n’a été faite par cet auteur.

Le source hors H, les réciproques m1 non friables de `F0\F1`, le complément non friable des deux ressources, les singletons/e1/p0, Gamma/T_A, les autres faces/nonbulk et la capacité du ledger entier restent ouverts. `e<=Q` et la positivité inconditionnelle de `Ecap`, non utilisés par les interfaces fermées ici, ne sont pas de nouveaux résultats annoncés. Aucune minoration de D_N, aucun contournement complet du mur de parité, aucune victoire. Source/olean/ledger PASS désormais gelés, aucun rejeu.
