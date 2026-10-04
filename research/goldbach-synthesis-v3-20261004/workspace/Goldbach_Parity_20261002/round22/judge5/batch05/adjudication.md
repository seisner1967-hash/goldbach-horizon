# Adjudication indépendante — batch05 — portée auxiliaire

Verdict réel `INDEPENDENT_BATCH05_AUX_PASS` : exactement deux enfants Lean, sans reprise, 17 théorèmes et six définitions, 23 audits `#print axioms`. Tous les audits ne dépendent que de `propext`, `Classical.choice`, `Quot.sound`. Aucun `sorry`, `admit`, déclaration `axiom`, `native_decide`, `unsafe` dans les deux sources ; aucun `sorryAx` de récupération dans les logs. Deux avertissements de style ΓBox, aucune erreur Lean. Aucun banc numérique exécuté.

## Exécution et provenance

Gate ROOT : `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\.arbor\sessions\parity\.coordinator\messages\round22_judge5_batch05_authorization.json`, SHA `2f67e55a754a883208f74b3d5b8fb90818bab45d4c90523d3fdd0bce1642bee6`, lue FULL a5c206. Une seule invocation du lanceur gelé d7ffee/session91759 → 1cffdc exit0. START `2026-10-03T12:37:05.313458+00:00` ; FIN globale `2026-10-03T12:37:59.696932+00:00`. Les deux commandes effectives sont conservées dans les START/FIN de module et le reçu.

| Module | START UTC | FIN UTC | Exit | Déclarations |
|---|---|---|---|---|
| GammaBoxBounds22 | 12:37:05.313458 | 12:37:27.615637 | 0 | 9 théorèmes + 3 définitions |
| GammaContourComponent22 | 12:37:27.615637 | 12:37:50.937286 | 0 | 8 théorèmes + 3 définitions |

ΓBox source `4874192b1c2ca9edc7262d8a46f9d4a1e339c565e5bb48fefbf4d6d100071edf`, log `51ec0900b9e0f6791268a86023661a5954e9ae9e10f3c5a3f1a2da011ea83162`, olean indépendant `4cb4d50f6d7dd8087e9d227d7052cb445527f018249dc3ffe6493ea2a87bfce3`.

ΓContour source corrigée `891454d4714e68039a0976e7eb9347e10653237f4608993b52b481cc95b0a3fe`, log `607a6e735964ffef61d4ae707a2ff503528311fc0df1722e0b6d5e42549e99b0`, premier olean `f9b5a9b2f47dd0ee03a58e6cd666d702ff5fc6eba39d07e89566a254df44648b`. Cette source n'avait pas de compilation auteur acquise. Son premier PASS actuel ne réécrit pas l'ancien échec de la source 244f20 : ancien source/log/FIN capturés et préservés.

Les seuls oleans locaux réutilisés sont ΓPrerequisites22 indépendant batch02 et ΓDerivative22 indépendant batch03, copies exactes readonly. Ils ne sont pas recompilés. LEAN_PATH contient le nouvel output, ce dossier readonly et les huit bibliothèques cache, aucun dossier olean auteur. Lean4.15 et mathlib9837ca9d demeurent fixés.

## Portée mathématique réellement acquise

ΓBox concerne la fonction à valeurs complexes définie par `exp(log(Y)·rho) * Complex.Gamma(rho+1)`, identifiée à `Y^rho Γ(rho+1)` sous Y>0. La borne de dérivée est déduite des bornes Γ et Γ′ indépendamment jugées ; convexité et théorème des accroissements finis donnent la borne Lipschitz sur 0≤Re(rho)≤1, Im(rho)≥gammaLo≥0, Y≥1. Les rayons rectangulaires donnent ensuite l'erreur de transport complète. Les hypothèses d'appartenance à ce domaine sont géométriques ; elles ne certifient ni existence/comptage d'un zéro, ni calcul intervalle d'une valeur Γ au centre. La formule de rayon est continue pour Y>0 ; sa validité comme majorant conserve Y≥1.

ΓContour concerne le même facteur le long de c+i·epsilon·t, c∈[−1/2,3/2], |epsilon|=1. La continuité réelle utilise la différentiabilité de Γ dans le demi-plan droit, avec la composition corrigée explicite. La borne Γ sur Re(rho+1)∈[1/2,5/2] et la monotonie de Y^Re(rho) donnent (27/5)·Y^(3/2)·exp(−πt/4) sous Y≥1,t≥0. L'intégrabilité exponentielle provient de la vraie intégrale Laplace déjà payée ; le changement d'échelle et l'intégrale impropre démontrée dans mathlib donnent sa primitive exacte. Mesurabilité via continuité, domination `mono'` et monotonie de l'intégrale établissent réellement l'intégrabilité L1 et la queue fermée

`(27/5) · Y^(3/2) · exp(−πT/4) / (π/4)` pour T≥0.

Ni l'intégrabilité finale ni le majorant final ne sont des prémisses libres. Les hypothèses libres de ce théorème sont les domaines Y≥1, c∈[−1/2,3/2], |epsilon|=1, T≥0. L'enveloppe définie est continue sur tout ℝ×ℝ ; sa positivité exige Y≥0 et son usage comme borne conserve le domaine précédent. Le module ne porte pas sur le produit avec ζ′/ζ, les côtés horizontaux, les résidus, le compte complet des zéros ou l'intégrale archimédienne globale.

## Conservation et lectures

PREEXEC SHA `1f884f40b1f14e095dfdc81aa6308224d6cfcee9dfa1e70d51816921a1dd649e` ; POSTEXEC SHA `61cd916351caeaafc94ac5e7bf65c9596ccd4bbb678b7d16b3a2e4437ede92dd`. Les 6707 inputs, 209 anciens fichiers Juge, 3089 archives et 32 captures ont été re-vérifiés sur leurs bytes actuels par la seule adjudication metadata. PRE/POST ont des bindings identiques, gate et captures conservées. Aucune ancienne compilation, aucune ancienne banque rejouée.

Sources propres FULL 9ca5d5/2e798b ; START/FIN/reçu FULL dd3834 ; vrais logs combinés stdout+stderr FULL ac5b92. PRE/POST : projections de headers 44d80f, hashes de tous bytes daa982, validation intégrale des bindings par ce helper ; aucune prétention raw FULL des gros JSON. Catalogue FULL59c79b et reads FULL10f5d7 avaient déjà clos la préparation. La lecture d4b140 a cherché un nom de log inexistant ; l'inventaire c35f98 et la lecture ac5b92 corrigent cet incident de lecture metadata, sans compilation supplémentaire.

Officiel ROOT avant observation : 66 modules /1109 déclarations auxiliaires avec définitions. Ce lot ajoute deux modules/23 déclarations ; 68/1132 demeure soumis à observation ROOT. Aucun crédit H1, C3, C5, C6, trace globale, coefficient N, D_N ou WIN. Le travail analytique et numérique global reste ouvert.

Adjudication créée à 2026-10-03T12:42:30.817526+00:00. Reçu effectif SHA `090538a9240c53bf248f7c9dbfef3fc708f5de272313e2d4733cb216ad252607`. Toutes les sources et tous les résultats effectifs restent immuables.
