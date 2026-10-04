# ROLE5 — inversion Mellin réelle, revue SOURCE indépendante

Statut : SOURCE/PAPER seulement, aucune invocation Lean, aucun import Python, aucun banc ou PREPARED. Baseline officielle après observation ROOT14 : 75 modules, 1223 déclarations auxiliaires ; ce fragment n'ajoute aucun PASS. Auteur ROLE3, reviewer ROLE5 distinct.

## Sources effectivement lues

Racine : `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role3\phase_mellin_inversion_source22`.

| Fichier | SHA256 | Lecture propre ROLE5 |
|---|---|---|
| ThermalGammaMellinInverse22.lean | 5271bbf9a9917a3ab61c6c7e0e747af4014e214b0867a9c81b43b5aa08fccec1 | FULL 55f808 et b42316 |
| source_contract22.md | 984f3e16d927b8d373b3c81af2848e18f77ffa7eb89efb7ab7c6ddf33accde01 | FULL df2642 |
| read_receipts22.json | a77e878bfc84be170ba4f8c52f743887d9afbcc57fd5cc82370f208ab51a6a0a | FULL 74ca2f |

Le texte contient exactement deux définitions, neuf théorèmes et onze `#print axioms` qualifiés. Pas de `sorry`, `admit`, déclaration `axiom`, `native_decide` ou `unsafe` dans le fragment. Ce contrôle textuel ne préjuge pas de l'élaboration ni de ses futurs axiomes transitifs.

## Chaîne mathématique et API

L'objet est le véritable noyau `expKernel x = exp(-x)` et la véritable fonction Gamma sur `s=2+it`. La continuité de Gamma découle de `Complex.differentiableAt_Gamma` : la partie réelle 2 exclut tous les entiers non positifs. La mesurabilité ne constitue pas une hypothèse libre.

La majoration `‖Gamma(2+it)‖ ≤ 2 exp(-(pi/4)|t|)` vient exclusivement de GammaPrerequisites22, déjà PASS indépendant et readonly. L'intégrabilité réelle positive du majorant est construite par `real_laplace_integrable` à `a=1`, `r=pi/4`. `Integrable.mono'` porte bien sur la mesure restreinte à `Ioi 0`. Le passage de la demi-droite négative utilise l'application mesure-préservante `t ↦ -t`, son préimage exacte de `Iio 0`, puis l'absence d'atome à 0 et l'union `Iic 0 ∪ Ioi 0 = univ`. Le changement de variable n'introduit ni signe ni facteur de Jacobien manquant.

`Complex.GammaIntegral_convergent` fournit réellement la convergence Mellin ; `GammaIntegral_eq_mellin` et `Gamma_eq_integral` identifient la transformée sur `Re(s)>0`. L'inversion mathlib réclame trois charges : MellinConvergent, VerticalIntegrable et ContinuousAt. Les trois sont construites dans cette source. L'application ne prend aucune identité d'inversion ou intégrabilité finale comme prémisse.

La conclusion est exactement, pour **x>0 réel**, `exp(-x) = (1/(2*pi)) ∫ Gamma(2+it) x^(-(2+it)) dt`, avec puissance complexe principale. La normalisation est celle de `mellinInv` et de l'inversion Fourier mathlib ; les inversions ne prétendent pas couvrir x=0 ou un taux complexe.

APIs propres contrôlées : MellinInversion.lean FULL 4b8969, SHA38cdb4e7f404dab6199f50b5a29a045ac2f9bbcc19d37a0430626f0914e5b49e ; MellinTransform.lean lignes35–96 et GammaPrerequisites22 lignes40–55/302–335 TARGETED 2867e9 ; Gamma/Deriv lignes35–44/75–85, Gamma/Basic lignes83–112/305–322 et IntegrableOn lignes220–231/695–707 TARGETED 59a6a9 ; L1Space.lean lignes432–444 TARGETED b26044, SHA7d041392ff5a34fb256b5ce97cc04b8c681919350c849647d4309bdc29af4a2a. Les sorties tronquées 2d8015 et 3b6479 ne sont pas revendiquées FULL.

La provenance readonly a été rehashée et projetée honnêtement b26044 : source `judge5/batch02_sources/GammaPrerequisites22.lean` SHA9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7 ; olean `judge5/batch02_attempt01/GammaPrerequisites22.olean` SHAfc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477 ; reçu ancien SHAa159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9, ligne Gamma exit0 et 23 audits standard. Aucun rejeu de cette compilation.

## Limites et première dette restante

Aucun déficit logique ou API précis détecté dans la lecture SOURCE de ces onze déclarations. Une compilation neuve autorisée resterait nécessaire pour valider les raccords Lean. Cela n'acquitte pas le théorème full-M pour la trace thermique : il faut encore identifier la véritable série Lambda au quotient zeta, justifier l'échange somme/intégrale, puis étendre l'identité au demi-plan complexe avec branches et domination locales.

Le contrat aval `Σ∫ ≤ 64/(pi*a²)` est cohérent sur papier avec `Σ 2 n^(-3/2) ≤ 4` et `∫ 2exp(-(pi/4)|t|) = 16/pi`. Les premières charges Lambda/Re2 utilisées pour ce prolongement sont encore SOURCE, distinctes du PASS Gamma ; elles ne figurent pas comme résultats démontrés dans ce fragment. La domination locale annoncée pour taux complexe et sa dérivée sont également PAPER. Aucun H1, quadrature uniforme en phase, coefficient N=10^8, correction des puissances premières, D_N ou WIN n'est acquis ici.
