# ROLE3 ψ — reçus honnêtes de lecture

FULL = contenu complet visible dans le résultat indiqué. TARGETED = uniquement
les lignes désignées/recherches visibles ; aucun fichier API tronqué n'est
présenté comme lu FULL. Les hashes sont des liaisons de fichier, pas une preuve
que toutes les lignes ont été examinées. Aucun résultat Lean nouveau ici.

| Document/source | SHA256 | Capture et portée |
|---|---|---|
| psi_c5_subcontract22.md | 2c0382c7069d7480fdb31d0c63baa56136e2ab4e0ac563de0f582899c2500c79 | FULL cc990e ; FULL 55858d |
| contour_formula22.md | 42faea33cdcd56c08f6fb593dbd42c5c293b8e72beb9c823db68e9576ac1edb7 | FULL e081fd ; FULL 55858d |
| judge5/h1_source_review01/review.md | 11b5cf745f50e75a10d670e55f39bb0e612902673a21bf13daa03bff41656e7f | FULL a2253e |
| GammaPsiCore22.lean | ecd6303389ce8cd60c87c9d79363e109f24841a18221dff46562d53759b460e8 | FULL 5ec540 |
| GammaPsiBetaLimit22.lean | 556cccecfc84e12f661fa46427d9a5ddc778b4d0f7d13eab398b35c2e9ff3ddd | FULL feffd5 |
| GammaPsiIntegral22.lean | 3703927fc8eacd8f8b33e590770473209c5e2289b34403d2ea601f42ef184615 | FULL 5ec540 |
| GammaPsiDuplication22.lean | 8a7f2c014866bfe49814c9310dfc012acd05e87c962b5976a32cf0fec9a2179f | FULL 5ec540 |
| ROLE4 ZetaReflection22.lean | 54e32a95a62929c7251bf130156adbc7da7d66ceb1cb77609382e33c025f4a42 | FULL 094735, non compilée |
| ROLE4 MellinThermal22.lean | 1396cb0a0045c621ea3e8f0f8b905c1c2a0af3ec33a351e4e7150542f38352fe | FULL 094735, non compilée |
| ROLE4 MellinThermalInversion22.lean | ad42b7bf8cd9b94e4f2c04125201b6a82b62821b1cb38652aa4e2f6c41a1df66 | FULL 094735, non compilée ; ancien ΓContour non acquis |
| ROLE4 ArchimedeanEndpoint22.lean | 390c324383a5cceda467128951b7606062b8eb58344b9bd6beec5753ae86896a | FULL 3e673e, non compilée |
| ROLE4 ArchimedeanTail22.lean | b5ae066392da14e8c8d1357e6259be2b4d57f8798f104770cc16fcba8ab1def7 | FULL 3e673e, non compilée |
| Ancien launcher G0 stage04 | 431e60bb7f61c6b73dc8917bd0f5346f7965876daaccfef7e8433131c15aec07 | FULL 4b4f26, modèle lu seulement, jamais rejoué |
| Juge batch02 reçu réel | a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9 | FULL 4b4f26, preuve readonly Γ |
| Nouveau banc component actual receipt | 2c7409087b6f4c18d9de616592d3c8b3274622bd05feb9fd12d54f93a0548f48 | FULL f568d3 : exit1, résultat absent, aucun PASS |

## API du cache sélectionnées

Racine : q356-canonical-binding-replay/.lake/packages/mathlib/Mathlib.

| Fichier/API | SHA256 | Capture / lignes TARGETED |
|---|---|---|
| Gamma/Beta.lean | 6ed0322724e35b5ac2b83b8b38516ed95fba308ee892e1baa622a49a13c722da | 1b22ff :47–144,227–338 ; 9d0bd9 :49–83 ; 3e673e :336–383,530–565 ; b3f9e2 :400–411 ; d5316c :414–439. Tentative8a0b1d tronquée, pas FULL |
| Harmonic/GammaDeriv.lean | f1d319c97dd25f23ff787680dc359cfabdaf19983e5bb9d8ce2cd22107b6e2da | d76e30 : contenu individuel entier visible, API Γ′(1) ; d46c1e : imports TARGETED |
| Pow/Real.lean | ab694db611eb09d0ee44704ae0225358823e2c0c1cf624847b9ec95f3fb4ea05 | aa8179 :306–318,526–536 ; 9d0bd9 :418–432 ; 7e7ecf/183cb4/b3d01c : rpow/divisions sélectionnées ; ab215c :103,125–144 |
| Pow/Deriv.lean | f03b4534a6afbfd5275433d2c56dce6627441e405353fab6813cae03672ea410 | aa8179 :165–178 ; b3f9e2 :179–207 ; d5316c :211–249 ; d46c1e : imports |
| MeanValue.lean | bc441942872e5fa25a45c38ab6f378d8f76de28809fdbacf78534136c4156acc | aa8179 :638–662 ; 9d0bd9 :590–613 ; 16d55a :651–655 |
| Integral/DominatedConvergence.lean | dcd3681d95530d0a475a260324501f3928ad03ea92cf7adca07fa1f2c0e472f3 | aa8179 :24–74 ; 16d55a :53–69,201–211 |
| Integral/IntervalIntegral.lean | a642c4dbf6c6a924b1b4f4ac94150d4ead8c06a9aa8b6e32192d26eb3be1fb2c | aa8179 :123–135 ; f16fb7 :84–89 ; 769a11 :237–263 ; c8e721 recherche partiellement tronquée |
| Function/Jacobian.lean | 0fda4e28d0030c4a72842ba6ece3b23ff0e3b60ab8ffa875bd1a699fc2f632f9 | 9d0bd9 :1196–1222 ; 5154c7 :1184–1199 ; signatures integral et integrable iff |
| Function/L1Space.lean | 7d041392ff5a34fb256b5ce97cc04b8c681919350c849647d4309bdc29af4a2a | 9d0bd9 :428–444 |
| StronglyMeasurable/Basic.lean | SHA lié dans l'inventaire API | f2cf3b :1520–1560, limite AE1542–1545 |
| Pow/Continuity.lean | SHA lié dans l'inventaire API | 0384e6 :105–121 ; d0695d recherche ciblée |
| Complex/RealDeriv.lean | SHA lié dans l'inventaire API | 68a898 :106–114 ; f16fb7 :88–117 |
| Deriv/Basic.lean et Deriv/Slope.lean | SHA liés dans l'inventaire API | e0cbbb :558–569 et72–84 ; 048eb2/01d942 recherches ciblées |
| SpecificLimits/Basic.lean | SHA lié dans l'inventaire API | 68a898 :44–68 |
| Topology/ContinuousOn.lean | SHA lié dans l'inventaire API | e0cbbb :430–438 |
| Complex/Log.lean et Pow/Complex.lean | SHA liés dans l'inventaire API | 5154c7/21aeb4 : log_ofReal, cpow_def, cpow_neg_one |
| Log/Basic.lean et ExpDeriv.lean | SHA liés dans l'inventaire API | 5154c7/21aeb4 : exp/log/injectivité/dérivée |
| Data/Complex/Exponential.lean | SHA lié dans l'inventaire API | 21aeb4 :242,1034,1051 |
| Integral/IntegrableOn.lean et SetIntegral.lean | SHA liés dans l'inventaire API | 5154c7 :686–694 ; bb8e13/d0695d : Ioc/Ioo recherchés |

Les incidents de recherche sont conservés : 01d942, b186c0, e1aa36, ab215c,
635fb1 ont rencontré un ou deux chemins devinés inexistants, puis les chemins
réels ont été retrouvés par rg/rg --files. 094735 cherchait Endpoint dans
h1_contour alors qu'il est dans role4 ; correction lue FULL3e673e. Ce sont des
erreurs de lecture fichiers, aucun appel Lean ni réfutation mathématique.

ROLE4 indépendante : FULL a84072 et41e749 sur les mêmes quatre SHA ; API
TARGETED60792f/c40ad1, recherches de chemins corrigées81a454. Ces reçus sont
rapportés comme evidence d'agent, pas comme mes propres lectures.
