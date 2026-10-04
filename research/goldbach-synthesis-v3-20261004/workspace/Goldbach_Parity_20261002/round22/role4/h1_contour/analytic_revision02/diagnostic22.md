# Analytic batch auteur01 — clôture réelle et réparation SOURCE

Le batch réel est `AUTHOR_ANALYTIC_BATCH_FAIL`. L'autorisation corrigée
39c59e2c33ecbb4682cc2c0bd8b264b1b22b92d06057ba6993003ea66d500f55 a été
consommée une seule fois. L'essai, ses sources, son manifeste et ses captures
restent intacts dans `../analytic_batch01/actual_attempt01`.

| Module | START UTC | FIN UTC | Exit | Audits | Olean |
|---|---|---|---:|---|---|
| GammaDerivative22 | 2026-10-03 10:40:22.681492 | 10:40:59.963181 | 0 | 8 standards | 0618f801c5feec7b760ba18ab3dddc960519b398dd1d1b719acc809132518125 |
| GammaBoxBounds22 | 10:40:59.963181 | 10:41:21.813547 | 1 | 8 standards, 4 avec sorryAx | absent |

`GammaContourComponent22`, `MellinThermal22` et
`MellinThermalInversion22` ne sont pas lancés. Le protocole STOP_FIRST_FAIL
est respecté : deux enfants, zéro retry, zéro nouvelle invocation mathématique
Python, aucune recompilation de GammaPrerequisites22 déjà jugé. ROLE4 totalise
cinq invocations Lean réelles, les trois essais Γ antérieurs compris.

ΓDerivative est un PASS auteur auxiliaire en attente de Juge indépendant.
Son théorème final dérive réellement la borne 19 exp(−π|Im(s)|/4) de Γ′ sur
1≤Re(s)≤2 par la rotation de Laplace, la convexité de Γ réelle et Cauchy.
Les quatre lignes de linter n'affectent pas les huit audits qualifiés standard.

## Erreur effectivement imposée par Lean

Le log ΓBox contient une seule ligne `error:` à 53:59. L'appel
`Gamma_differentiableOn_rightHalfPlane.differentiableAt rightHalfPlane_isOpen`
donne une preuve `IsOpen rightHalfPlane` à l'argument qui attend
`rightHalfPlane ∈ 𝓝 (rho + 1)`. Les quatre déclarations contaminées par
`sorryAx` sont hasDerivAt_weightedGammaTerm et ses trois conséquences sur
la norme dérivée, la constante de Lipschitz et le rayon de boîte. Il n'existe
pas de balise sorry dans la source ; l'échec d'élaboration produit ces
dépendances et interdit de valider le module. Ce log ne démontre aucun
contre-exemple analytique ni une obstruction de parité.

La réparation distincte `GammaBoxBounds22.lean` établit d'abord
`hmem : rho + 1 ∈ rightHalfPlane` avec Re(rho)≥0, puis fournit
`rightHalfPlane_isOpen.mem_nhds hmem` à `differentiableAt`. Les douze
énoncés, leurs hypothèses et leurs douze audits restent identiques.
La révision a seulement le statut SOURCE_ONLY, sans compilation, gate,
nouveau banc ou certification du rayon.

Les signatures sont lues dans le cache mathlib4.15 :

- Analysis/Calculus/FDeriv/Basic.lean 517–519 :
  DifferentiableOn.differentiableAt prend `hs : s ∈ 𝓝 x`.
  SHA b9492e840d6952cbac27ee1e3eeb193f73908032465a78a2d3c8f988ff07c93c.
- Topology/Basic.lean 759–760 : IsOpen.mem_nhds prend la preuve
  `hx : x ∈ s` et retourne `s ∈ 𝓝 x`.
  SHA 8def33217c240cb0f3247974fbe9bc6eb8dc2eb74f8d8a09194419c85d892f02.

Ces lectures sont TARGETED et ne prétendent pas être des lectures FULL du cache.

## Traces et périmètre des lectures

Receipt réel SHA 939122be1e498225f47b15d79bb3357a68573bf306dffad37e31ba54a01ba613.
PREEXEC SHA 17150370c55b2aaa3a65b973f4f20d63f79742c3100afbc1cfff1b278f4bef43.
START SHA 803fe8661c859a6dc15d785016d171e7f2b188d61f5176e868ec35b47bc18bc0.
POSTEXEC SHA 670fedfad0e6131a0b50f5eda4cf50b2fc769da7efad36917dc44d35b19d13bd.
Les 19 captures, 6517 bindings et 3089 archives ont été vérifiés en bytes
avant et après ; aucune mutation.

Log ΓDerivative SHA 1458fd3ab5cbcdeea6b19166c1f21e254d336e1eb2d1a0e7bf8d11b1abbad352.
Log ΓBox SHA 271fb861b82d3a2d0a395ad4178d2fc49becf334324da29fab22ccc9f7ed426a.
Les deux stderr sont vides (SHA e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855).
FIN ΓDerivative SHA 6514ebf5e7a7c7378423ed59d4ab2729a506d4b31f5f99c21a5d1446d809127e.
FIN ΓBox SHA 9d59f7c1b7565b6cf4ebf4914ba7b230ee743687785b0f5038692c1318853017.

Logs FULL db3f16 ; receipt/PRE/POST/START et deux child START FULL9c4e9d ;
les deux FIN relus FULL0bbf2f. La lecture agrégée2789b3 était partiellement
tronquée sur PRE, d'où la lecture complète9c4e9d. Le premier appel db3f16
avait demandé un nom de receipt erroné actual_receipt.json ; cet incident de
lecture, corrigé en receipt.json, n'est pas un échec Lean supplémentaire.
Source ΓBox originale FULLd2bbc7, révision entière FULL5f3d29.

La vraie formule thermique H1, χ/ψ et C5, les bornes uniformes du produit
G·F, les résidus et bords, la contribution additive N et la borne D_N restent
ouverts. Les 121 déclarations aval SOURCE ne reçoivent aucun crédit par ce
batch. Ni victoire ni résultat global n'est revendiqué.
