# Préparation indépendante batch07 — SOURCE uniquement

Lot nouveau de huit modules, 74 théorèmes et neuf définitions : 83 déclarations/83 futurs audits qualifiés. Aucun Lean, probe ou calcul numérique dans cette préparation. Une gate ROOT spécifique reste nécessaire avant l'unique éventuel essai `batch07_attempt01` : huit enfants maximum, ordre ci-dessous, arrêt au premier FAIL.

| Module | Théorèmes | Définitions | SHA256 source exacte |
|---|---:|---:|---|
| ZetaReflection22 | 6 | 1 | cc39bd76e00889d154a3acefea0588ca1ec7408836210f68752d5d2055f8ca2f |
| GammaPsiDuplication22 | 2 | 0 | 0491177c6cfc1ef35b28796be404a3ca7975bac357cc6551b80d12333726812e |
| GammaPsiReflection22 | 5 | 0 | 8e070c18a483ac71703f66b80dbcf4129f0f16ada8f2a933497655b3a7cdaa30 |
| ContourChiPsi22 | 9 | 1 | a90d536187fe342d01cf913a56c80a34e6846eb273a533bcdd843289f7d83248 |
| ContourChiScaled22 | 8 | 2 | d0aa03290fe806f9c84c0311a7e07a2fe0737148c9c1de7c80876118fb7a64d7 |
| PsiKernelEnvelope22 | 8 | 1 | 949c6fc0d895003b522518e18ae89bdf6b5062448d5273f146685645afb72ef8 |
| PsiKernelDomination22 | 19 | 2 | 80b85c14c7db79121f7c9cb003edf97a7d5e947f785ce8402f910ea93aad48bc |
| PsiMixedFubini22 | 17 | 2 | d143b0fbdf795a1b400f737274a5eae5c8c5bba0c2e4ecaf145d86932df0b250 |

La copie Reflection vient de `B/round22/role3/revision_reflection07/ZetaReflection22.lean`. Les sept autres copies exactes viennent de batch06/sources, avec les mêmes originaux ROLE3 gelés. La création physique native 30bc57 a contrôlé leurs hashes. Les sept énoncés Reflection et leurs domaines restent inchangés. Les hid/harg/hf typés fixent le point s ; la composition de Gamma utilise explicitement harg ; `Function.comp_apply`, les normalisations des produits et `← sub_eq_add_neg` remplacent le lemme absent ; `ring` après fermeture du but est retiré. Source originale lue entière 8431ee et copie propre ddb5ee ; handoff review39a12f et reads f57032. Le statut est SOURCE, pas PASS.

Les APIs du cache mathlib ont été lues TARGETED : Pow/Deriv 86–112 (37d550), FDeriv/Add 666–684 et Comp 90–112 (8c2eb0). Elles demandent explicitement le point de différentiabilité, la non-annulation de la base pour const_cpow, puis l'argument de composition. Le repérage 77be8a montre des références à `sub_eq_add_neg` et `comp_apply`, sans prétention de lecture FULL de ces modules. Le builder ancien, tronqué dans l'agrégat dd7cd1, a été relu entièrement 88113a. Ces lectures de texte ne remplacent pas Lean.

## Audit mathématique SOURCE

Reflection utilise la vraie équation fonctionnelle de `riemannZeta` en un voisinage ouvert de s. Pour −1<Re(s)<0, le cosinus et Gamma(1−s) sont non nuls, la puissance de 2π est non nulle par l'exponentielle, ζ(1−s) est non nulle grâce au vrai EulerDirect indépendant. La dérivation du produit et le quotient utilisent ces dénominateurs établis. Aucun postulat de trace ou de non-annulation libre n'est ajouté. Le nouvel essai décidera si les corrections d'élaboration suffisent.

Duplication dérive la véritable identité de Legendre, puis divise par Gamma(z), Gamma(z+1/2), Gamma(2z), puissance et racine de π non nulles sous Re(z)>0. Ce fichier a seulement PASS auteur antérieur ; aucune compilation indépendante obtenue. ΓReflection dérive les Gamma décalées 1±s/2 dans le demi-plan positif, prouve la non-annulation du sinus et de s dans la bande, et déduit la formule de ψ. Aucun argument Gamma négatif n'est différentié sans charge.

ChiPsi concerne la même `contourChi` réelle, normalise log(2π) sur l'axe réel positif, puis utilise duplication, reflection et les vrais théorèmes P1 indépendants. Le numérateur exponentiel reste apparié près de zéro ; l'intégrabilité n'est pas tirée d'une somme de termes séparés divergents. Les passages d'intégrales utilisent l'intégrabilité effective des deux noyaux P1. Scaled transporte cette intégrabilité sous u=2v, avec injectivité, image Ioi et valeur absolue du Jacobien 2 explicites.

Envelope construit E(t,v)=(14+4|t|)exp(1−v)+8exp(−3v/2), sa positivité, sa continuité et son intégrabilité en v. Domination part du numérateur N(t,0)=0 et de la dérivée bornée par 7+2|t| ; les accroissements finis donnent |N|≤(7+2|t|)v. Le dénominateur 1−exp(−2v) est positif pour v>0, au moins v/2 près de zéro et 1/2 pour v≥1. Les bornes sont donc 14+4|t| et 8exp(−3v/2), puis E, toutes dérivées du noyau concret.

Mixed utilise précisément `gammaContourFactor Y (-1/2) 1 t * contourPsiScaledKernel (leftChiPoint t) v`. La récurrence Gamma avec norme de 1/2+it au moins 1/2 donne la borne 4Y^(−1/2)exp(−π|t|/4), valable ici Y>0. Il ne réutilise pas indûment la borne de bande Y≥1. L'enveloppe mixte est un produit de deux fonctions exponentielles intégrables, avec le facteur |t| payé par la vraie intégrale Laplace. La continuité et les dénominateurs non nuls fournissent la mesurabilité forte ; `Measure.prod_restrict` identifie la mesure, `mono'` établit l'intégrabilité réelle, puis `integral_integral_swap` conclut Fubini. Le helper générique `integrable_abs_extension hf` a une prémisse normale ; ses utilisations finales fournissent de véritables intégrabilités exponentielles, pas la cible à prouver.

Ces vérifications reprennent le précédent audit C5 b2458e4… et la préparation batch06 source conservée. Aucun théorème final concret ne prend Fubini, P1, le majorant Gamma, celui du noyau ou la cible D_N comme prémisse libre. La compilation de ces modules reste ouverte. Mellin, Arch global, le passage x=exp(v), les orientations/normalisations finales, les côtés horizontaux, le compte complet des zéros et la certification intervalle des primitives ne sont pas des conclusions de ce lot. Aucun banc numérique ne finance ses preuves.

## Dépendances et conservation

Huit dépendances locales réutilisées uniquement par oleans indépendants exacts readonly : GammaPrerequisites22 (batch02), GammaDerivative22 (batch03), GammaBoxBounds22 et GammaContourComponent22 (batch05), GammaPsiCore22/BetaLimit22/Integral22 (batch04), ZetaEulerDirect22 (batch06 PASS5). Aucune n'est recompilée. Le reçu global batch06 est FAILED, mais son row Euler est PASS indépendant réel, exit0, olean555b108… et cinq prints standards. Le builder contrôle ce row et les bytes, sans demander un faux PASS global.

Les lots01–06 restent clos. L'ancien Reflection54e32… FAIL et ses dix diagnostics/2recovery sont préservés. Les sept modules non invoqués batch06 reçoivent un premier essai éventuel, pas un replay. Tous les anciens fichiers Juge et 3089 archives sont liés et hashés. Aucun olean auteur dans LEAN_PATH : nouvel output, huit copies readonly et huit bibliothèques cache seulement. Dup05 olean auteur est lié comme provenance, sans servir de dépendance.

Lean4.15, Python cache fixé et mathlib9837ca9d restent inchangés. La fermeture d'import inclut Init implicitement et lie les vrais fichiers .lean/.olean des huit packages et de Lean ; cette fermeture est HASH_AND_IMPORT_METADATA_ONLY, pas audit mathématique FULL de mathlib. Le builder ne possède aucun subprocess ; le launcher unique crée captures exactes, PREEXEC, START global/par module, commandes/logs, FIN, POSTEXEC, receipt et ferme au premier échec. Aucun retry caché. Ces outils devront être lus entièrement avant leur usage respectif.

Lectures propres FULL : ddb5ee/a31e1c/f3e263/dbab7a/90624d/efbf10/c95d0e/63855c. Anciennes sources et reçus indépendants ont leurs lectures FULL et hashes exacts dans read_receipts ; ce sont des références préservées, sans nouveau replay. Les gros manifestes doivent être présentés par projection honnête et hashes de tous bytes, pas comme raw FULL.

Officiel ROOT après observation réelle 5dad0a : 69 modules /1137 déclarations auxiliaires incluant définitions. Huit PASS éventuels ajouteraient 83, soit 77/1220 seulement après résultats et observation ROOT. SOURCE ne change aucun compte. H1, C5 global Arch, trace globale, coefficient N, D_N et WIN restent ouverts.
