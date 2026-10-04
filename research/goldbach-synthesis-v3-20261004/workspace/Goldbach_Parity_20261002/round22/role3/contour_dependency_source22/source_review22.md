# Réparation distincte ΓContour — SOURCE uniquement

Cette copie corrige deux erreurs d'élaboration effectivement observées dans
`role4/h1_contour/analytic_batch02/actual_attempt01`. Aucun compilateur,
import Python, probe ou calcul numérique n'a été invoqué pour cette copie.
Elle n'est pas PREPARED, n'a pas de gate et ne reçoit aucun crédit PASS.
Les fichiers historiques, captures et sources ROLE4 restent inchangés.

Source nouvelle : `GammaContourComponent22.lean`, SHA256
`891454d4714e68039a0976e7eb9347e10653237f4608993b52b481cc95b0a3fe`.
Base conservée : SHA256
`244f20f0d0198101b6b2a27841b273b01f7c52f28a38b7b51b4db588446f4265`.
Onze déclarations explicites et onze `#print axioms` qualifiés sont conservés.
Aucune hypothèse analytique supplémentaire, aucun axiome ajouté.

## Les deux changements

La composition de continuités spécifie maintenant explicitement
`f := fun u : ℝ => gammaContourPoint c epsilon u + (1 : ℂ)` et `x := t`.
Une proposition intermédiaire donne la continuité réelle de ce chemin à t.
Dans le journal ancien, l'inférence avait choisi le chemin partiel `HAdd`
avec point de base 1 ; elle demandait donc une proposition d'un autre type.
La continuité de Gamma vient toujours de sa différentiabilité dans le vrai
demi-plan droit, avec `0 < Re(point(t)+1)` payé par `c ≥ -1/2`.

L'évaluation de la queue exponentielle utilise
`_root_.integral_exp_neg_Ioi`, qui est le nom réel du théorème du cache.
Le changement affine positif reste `integral_comp_mul_left_Ioi` ; son
jacobien est `a⁻¹`. La valeur obtenue est toujours `exp(-a*T)/a`.

Ces erreurs concernaient des types/noms d'API. Elles n'étaient pas des
contre-exemples mathématiques ni une manifestation du mur de la parité.

## Preuves et portée conservées

L'objet est le véritable `weightedGammaTerm Y (c+i*epsilon*t)`, avec
`weightedGammaTerm Y rho = exp(log(Y)*rho)*Gamma(rho+1)`.
La borne de Gamma sur `1/2 ≤ Re(rho+1) ≤ 5/2` et la monotonie de `Y^Re(rho)`
pour `Y ≥ 1` donnent la majoration uniforme
`(27/5)*Y^(3/2)*exp(-(pi/4)*|Im(rho)|)`.
La substitution signée `|epsilon|=1` conserve les deux queues verticales.

L'intégrabilité de l'exponentielle est dérivée de la vraie intégrale de
Laplace avec exposant 1, puis restreinte à `Ioi T`, `T ≥ 0`.
La continuité de l'objet fournit sa mesurabilité ; la domination positive
fournit son intégrabilité. L'inégalité d'intégrales de normes et la valeur
de la queue exponentielle donnent la même enveloppe fermée et continue
`((27/5)*Y^(3/2))*exp(-(pi/4)*T)/(pi/4)`.
Aucun majorant libre ou intégrabilité de la cible n'est pris en prémisse.

Imports exacts conservés : `GammaBoxBounds22` et
`Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`.
Le premier dépend de `GammaDerivative22` puis `GammaPrerequisites22`.
Le reçu auteur de GammaBox, réellement lu ici, donne exit0, source
`4874192b1c2ca9edc7262d8a46f9d4a1e339c565e5bb48fefbf4d6d100071edf`,
olean `4cb4d50f6d7dd8087e9d227d7052cb445527f018249dc3ffe6493ea2a87bfce3`
et douze audits standards. Cette provenance auteur n'est pas remplacée
par une affirmation de validation indépendante non lue ici.

La copie ne borne pas `zeta'/zeta`, ne prouve pas les résidus, C5, H1 ou
l'extraction du coefficient N et ne paie aucune charge de D_N. NO_WIN.

## Reçus de lecture honnêtes

Les identifiants ci-dessous sont les sorties réelles des commandes de
lecture PowerShell ; toutes ces commandes ont exit0.

| Fichier | Portée | Reçu | SHA256 |
|---|---|---|---|
| ΓContour base244f20 | FULL | ddb896 | 244f20f0d0198101b6b2a27841b273b01f7c52f28a38b7b51b4db588446f4265 |
| Ancien journal ΓContour | FULL | 6179bc | 1e72a122b34680b073571e620e16125e55ce4a7b6c20ed43fdd62128bd588510 |
| Topology/Basic.lean | TARGETED lignes1438–1461 | 1e9e84 | 8def33217c240cb0f3247974fbe9bc6eb8dc2eb74f8d8a09194419c85d892f02 |
| ImproperIntegrals.lean | TARGETED lignes1–61 | 1e9e84 | 4356decb7750e59fc41f86931c9b13c95f66cb9c2e53c72b639a8e4f4fcfcd23 |
| IntegralEqImproper.lean | TARGETED lignes1086–1111 | c0c82a | b7566d4908de6f28c73b0490a6bd79c3990bde03007f1b5b291d1b11a8ef1533 |
| GammaBox source | FULL | 390442 | 4874192b1c2ca9edc7262d8a46f9d4a1e339c565e5bb48fefbf4d6d100071edf |
| GammaBox FIN auteur | FULL | e54739 | eff512587a9b8610a637f2039bd93a535c698b916d9aa77d8cc415d0b946142b |
| Nouvelle copie ΓContour | FULL après écriture | 202017 | 891454d4714e68039a0976e7eb9347e10653237f4608993b52b481cc95b0a3fe |

Les recherches `rg` 676a24/1cb7d9/bac72c/390442 sont des inventaires ou
lectures ciblées ; elles ne sont pas revendiquées comme lectures FULL
des répertoires ou de leurs autres documents. Aucun nouveau paquet de
compilation, manifeste PREEXEC ou launcher n'a été exécuté/préparé ici.
