# ROLE5 — Mellin complexe, revue SOURCE indépendante

Statut : **SOURCE mathématiquement cohérente dans le domaine Re(w)>0 ; élaboration et axiomes non vérifiés par un nouveau compilateur**. Aucun déficit logique précis identifié dans cette lecture. Aucune préparation, invocation Lean, import du candidat, sonde ou vérification numérique. La revue est close à réception du handoff prioritaire BORD04 ; elle ne confère aucun PASS. Baseline officielle 82 modules / 1367 déclarations auxiliaires, inchangée.

Paquet gelé : `D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_source02`. Lectures propres, texte complet non tronqué : cœur `046a49`, extension `e150e7`, contrat/catalogue/handoff `bbcc8b`, lectures auteur `909eb6`.

| Fichier | SHA256 | Portée propre |
|---|---|---|
| ComplexGammaMellinLocal22.lean | e54cac5b2ab3996eb7bb86165448e0eff4c837b2fbda0af923e454962e526e08 | FULL, 22 déclarations = 16 théorèmes + 6 définitions |
| ComplexGammaMellinHolomorphy22.lean | 9d3d050fab541086f1bf9932aa51d240dd3a72fcb194412f38e997ebeedd9d4a | FULL, 15 déclarations = 11 théorèmes + 4 définitions |
| source_contract22.md | 32e7a776c10ae151a80960d27861667f7f8a39eb3f8a639b4cd39ae36960b5b4 | FULL |
| source_catalog22.json | 0360d3763e0ff0f9dd2c7a942e65d3d9d24ba38570e341b69c23d5329e1fdfbc | FULL |
| source_handoff22.json | 2c10db3fae90cf309f03c28018e2e52b3acefdf624501cd453bdd7560f8b6634 | FULL |
| source_read_receipts22.json | 9d6e09338f491015d9920f4ff8da005d963194bf8f4fbca75b856bdd745d981b | FULL ; les scopes auteur restent distincts des miens |

Les 37 noms et 37 `#print axioms` sont présents textuellement : 27 théorèmes, 10 définitions. Leur résultat futur, y compris les listes vides éventuelles, reste inconnu. Pas de conclusion acquise à partir de la seule présence de ces commandes.

La chaîne utilise la vraie `Complex.Gamma`, le `cpow` principal et s=2+it. Re(w)>0 fournit effectivement slitPlane et w≠0. Avec η=(π/2+|Arg(w)|)/2 et δ=η−|Arg(w)|>0, la rotation Γ déjà indépendante et la norme exacte du `cpow` donnent C exp(−δ|t|), C=‖w‖⁻² sec²η. Les demi-droites sont intégrées à l'aide de la vraie intégrabilité Laplace ; le transport par négation et le point de mesure nulle paient la droite entière. L'intégrabilité n'est pas une hypothèse libre du théorème final.

Le majorant dérivé est réellement local : une boule centrée en w₀ conserve Re(z)>0, ‖z‖≥‖w₀‖/2 et |Arg(z)|≤r<η. La même rotation fournit un majorant C₀(2+|t|)exp(−δ₀|t|) uniforme sur cette boule, δ₀=(π/2−|Arg(w₀)|)/4>0. Les moments Laplace 1 et 2 paient son intégrabilité. La dérivée du noyau est (−s)K/z ; les arguments de différentiation paramétrique donnent mesurabilité, intégrabilité au centre, domination locale et dérivée point par point. Aucune intégrabilité ou dérivée globale n'est offerte en prémisse.

L'identité complexe est ensuite obtenue par analyticity sur le demi-plan ouvert et principe d'identité sur ce domaine préconnexe. L'accord positif réel provient du vrai PASS20 `real_exp_eq_Gamma_integral`, non d'une nouvelle hypothèse d'inversion. Les taux 1+1/(n+1) tendent vers 1 tout en restant distincts de 1 ; le point d'accumulation appartient au domaine. Aucune RH ni information sur les zéros n'intervient.

API primaire locale Mathlib 4.15/9837ca9d, lectures **TARGETED** : ParametricIntegral.lean 281–302 et IsolatedZeros.lean 265–284 (`541bd5`) ; Pow/Real.lean 596–618 et CauchyIntegral.lean 569–583/601–628 (`541bd5`) ; Pow/Complex.lean 87–100, ΓPrerequisites 41–52/175–178/267–278 et PASS20 133–138 (`111020`) ; Pow/Real.lean 286–289 et MetricSpace/Pseudo/Defs.lean 705–707 (`599fa8`) ; **SpecialFunctions/Complex/Arg.lean** 373–377/542–550 (`78a98e`, SHA 2617fea0f21bd7d4b718fe6fc24565a99dfc9b9ac7ee76e23fee00a1052bf89d). La sortie `85fb46` tronquée est exclue des lectures FULL. Le chemin Analysis/Complex/Arg.lean donné au premier petit extrait n'était pas le chemin de ces signatures ; les signatures pertinentes ont été relues au bon chemin dans `78a98e`.

Dépendances indépendantes seulement, lecture de source ciblée et conservation byte-hash `111020`, sans reprise : PASS20 ThermalGammaMellinInverse22 source daad8b5d5fb1181bfc714e1b470edd7d9a6ae07e9a1b76c384481964a42caf91, olean e9442776bb512a4f83391b63402a1dc86bce61070dfc386bc8b6873af521ce24, reçu 28a07d17e88dbb09157c5958306efd557cd9d4727dd4948b336aaad4ee48d68c ; ΓPrerequisites indépendant source 9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7, olean fc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477, reçu a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9. Chemins liés : judge5/batch20/sources, batch20/batch20_attempt01 et ses PREEXEC_FILES/23_GammaPrerequisites22.lean, 25_receipt.json. Ces olean ne sont pas une preuve d'élaboration des deux nouveaux modules.

Limites : les constantes dégénèrent lorsque |Arg(w)| approche π/2 ; la boule est existentielle, sans rayon calculable explicite ici. Les formules quantitatives de queue annoncées dans le contrat restent PAPER, hors des 37 déclarations Lean. Ce paquet ne paie ni échange avec Λ ou ζ′/ζ, ni corrélation signée, ni correction des puissances de premiers, ni frontière/ledger, ni producteur du coefficient N=10⁸, ni D_N. L'enveloppe uniforme en phase et la cible restent ouvertes. Aucun WIN.
