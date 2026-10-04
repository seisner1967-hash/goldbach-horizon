# Batch04 clos — vraie P1 auxiliaire certifiée

INDEPENDENT_BATCH04_AUX_PASS : trois enfants neufs Core→BetaLimit→Integral,
52prints exacts,44théorèmes et8définitions. Launcher841fed/session76496,
achèvement431075 exit0. Gate réelle 66b47ab7d2d5ada4a81d8a34c2354c26967d2bd7997064d77f32757b5dc1040a.
Logs, START, FIN et receipt lus FULL8657fd, sans troncature.

- GammaPsiCore22 : 2026-10-03T11:40:20.031839+00:00 → 2026-10-03T11:40:52.083426+00:00, exit0.
- GammaPsiBetaLimit22 : 2026-10-03T11:40:52.090499+00:00 → 2026-10-03T11:41:26.232271+00:00, exit0.
- GammaPsiIntegral22 : 2026-10-03T11:41:26.232271+00:00 → 2026-10-03T11:41:42.045503+00:00, exit0.

Tous les prints ne dépendent que de propext, Classical.choice et Quot.sound.
Core porte quatre warnings de linter ; BetaLimit et Integral aucun. Aucun
sorry/admit/axiom ajouté, native_decide, unsafe ou cible supposée. Les trois
oleans sont produits dans le nouveau dossier du lot ; les imports locaux des
deux derniers utilisent ces sorties neuves. Aucun olean auteur, ancien compile,
retry, probe ou banc numérique. Des SHA identiques aux sorties auteurs n'effacent
pas la provenance distincte des nouvelles commandes START/FIN.

La conclusion P1 payée est, pour Re z>0,
Γ′(z)/Γ(z)=−γ_E+∫_(u>0)(exp(−u)−exp(−zu))/(1−exp(−u))du,
avec intégrabilité du véritable intégrande. Core identifie le vrai quotient Γ
et sa limite ; BetaLimit construit le majorant concret intégrable
2(t^(Re z−1)+1)+‖z−1‖(1+(1/2)^(Re z−2)), sa mesurabilité et DCT.
Integral prouve l'image, l'injectivité, la dérivée signée et le Jacobien absolu
de t=exp(−u), puis transporte l'intégrabilité avant la conclusion. Aucune
prémisse libre de domination, intégrabilité ou formule Ψ cible. L'égalité
intermédiaire pour tout z emploie l'intégrale Bochner totalisée ; le domaine
Re z>0 est payé séparément pour donner la véritable identité intégrable.

L'adjudication documentaire revérifie les6648 entrées,134 anciens fichiers
Juge,3089 archives et26 captures byte par byte, plus la gate. PRE/POST sont
entièrement parsés et liés ; aucune lecture brute FULL des grands JSON ou FULL
mathématique de toute la fermeture n'est revendiquée. Conservations vraies.
Receipt : 228b0958ecac8037e1776cf5cc32db340a8f52944c1e9cd398415dd9f0415c5d.

Delta proposé après observation ROOT :3modules/52déclarations,66/1109 depuis
63/1057. Cette P1 auxiliaire ne paie pas le couplage à la fonction test, le
Fubini global/C5, duplication horslot, Weil, contours infinis, compte complet
des zéros, coefficientN, D_N ou WIN. Aucun autre compilateur anticipé.
