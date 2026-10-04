# Batch auteur analytique 01 — préparation SOURCE ONLY

Le batch vise cinq modules et 47 déclarations qualifiées, dans cet ordre :
GammaDerivative22 (8), GammaBoxBounds22 (12), GammaContourComponent22 (11),
MellinThermal22 (12), MellinThermalInversion22 (4). La version du troisième
module est exclusivement `h1_contour/gamma_revision01`, SHA 9124b02b… ;
l'original 084a1908… demeure intact. Les copies portent leurs noms de modules
usuels dans `sources/`. Aucun de ces cinq modules n'est actuellement compilé.

GammaPrerequisites22 est une dépendance déjà compilée et jugée : source
9f5e5fe1… et olean fc0dad0b… du vrai batch indépendant 02. Source et olean
sont copiés avec vérification des octets. Le lanceur ne recompile pas Γ.
Le reçu indépendant a été lu intégralement (`57db21`), ainsi que son FIN
Γ (`af5253`). Il n'est pas rejoué comme une nouvelle mesure.

Le builder PowerShell effectue uniquement copies, extraction d'en-têtes
d'importation, résolutions source/olean existantes, SHA256 et vérification
des 3089 archives protégées. Il fige la fermeture transitive réelle des
imports et les deux octets de chaque module cache. Ce contrôle d'en-têtes
et de bytes ne prétend pas une lecture intégrale des APIs du cache.
Les cinq sources ont été lues FULL : 57db21, 57db21, aac0f5, 80a3b6, af5253.
Les lectures API mathématiques antérieures restent dans les reçus v3/v4.

Le nouveau composant numérique a échoué techniquement sur JSON au-delà
de 4300 chiffres, sans résultat complet et sans contre-exemple établi.
L'ancien banc Γ H2 est conservé comme provenance auxiliaire, sans nouvel
exécution ou crédit H1. Selon l'instruction ROOT du 2026-10-03, une gate
distincte peut autoriser ces preuves auxiliaires malgré ce seul échec de
sérialisation : le lanceur exige explicitement les deux vérifications ROOT,
leurs hashes, la compatibilité de portée et l'autorisation bornée.

Le lanceur demeure non exécuté. Il vérifie la gate exacte, le manifeste,
tous les bindings, les runtimes fixés et les archives ; capture les cinq
sources, la dépendance Γ, le lanceur, le builder, les lectures, la préparation,
les preuves de provenance, le manifeste et la gate avant START. L'actual
directory exclusif consomme la seule tentative. Chaque enfant a START/FIN,
stdout/stderr, exit, hash olean s'il existe, audit de toutes les déclarations.
Le premier exit non nul, erreur ou audit non standard arrête le batch ;
les modules restants sont explicitement non lancés. Aucune relance implicite,
aucun probe, installation, banc mathématique ou ancien run n'existe ici.

Un succès éventuel serait seulement AUTHOR AUX PASS PENDING JUDGE.
H1/C3/C5/C6, trace globale, coefficient N, cible D_N et WIN restent ouverts.
Le pôle et Euler/Λ/Fubini sont des sources distinctes pour un prochain batch.
