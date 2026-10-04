# ContourChiPsi revision09 — SOURCE seulement

Source finale : ContourChiPsi22.lean, SHA30c44bb1e376c32c28201e79adaad55043143081d56d4429c6d0b30e8f217540, lecture FULL7f728e. L'original SHAa90d536187fe342d01cf913a56c80a34e6846eb273a533bcdd843289f7d83248 reste intact ; il a été lu FULL510638 et son hash vérifié92d3e1 puis7f728e. Le Juge a signalé ces motifs à titre préventif après l'échec technique du module GammaPsiReflection précédent. Aucun échec de compilation de ContourChiPsi n'est présumé.

La source conserve neuf théorèmes, une définition, les dix noms qualifiés et les dix commandes `#print axioms`. Les énoncés et les domaines sont strictement conservés. En particulier la bande −1<Re(s)<0, le vrai contourChi défini dans ZetaReflection, les deux arguments Gamma/Psi, les intégrales sur Ioi0, les preuves de non-annulation et les prémisses d'intégrabilité effectives ne sont pas changés.

Deux preuves sont ajustées :

- Dans deriv_contourChi_sine, la dérivée issue des compositions est simplifiée avec Function.comp_apply et id_eq, ainsi que les facteurs1 et0, avant linear_combination. La règle de chaîne et les preuves analytiques existantes sont conservées.
- Dans contourChi_logDeriv_direct, la division est prouvée d'abord dans une identité de corps locale pour des variables a,g,z non nulles. Elle est ensuite instanciée explicitement par cpow, Gamma, sa dérivée, sin, cos, log et π/2. Les trois non-annulations hp,hg,ht déjà construites paient les hypothèses de l'identité locale. Aucun lemme global, axiome ou prémisse analytique supplémentaire n'est ajouté.

Les autres preuves sont identiques, notamment le raccord logarithme/duplication/réflexion, l'identité de l'intégrande paire et les vraies preuves d'intégrabilité venant de P1. Cette source ne prend pas Fubini global, C5 ou un majorant libre en prémisse. Sa dépendance GammaPsiReflection revision08 est SOURCE non compilée à cette date ; la compilation et l'audit indépendant restent requis.

API consultée TARGETED92d3e1 : Mathlib/Analysis/Calculus/Deriv/Basic.lean, SHA9576d3ea4e2988124154e7ddf538e48b2d6b6d5eca409cbbe31128759374f1d6, lignes356–370 et552–570. Les signatures HasDerivAt.unique et HasDerivAt.congr_of_eventuallyEq confirment la normalisation employée. Aucune lecture FULL de ce fichier API n'est revendiquée.

Zéro invocation Lean, probe, parseur ou calcul Python pour cette révision. Aucun fichier gelé ou fichier du banc numérique actuellement actif n'est modifié. Le banc unique continue avec son watchdog3600s et sa limite2147483648octets. H1/C5 global, coefficientN, D_N et victoire restent ouverts.
