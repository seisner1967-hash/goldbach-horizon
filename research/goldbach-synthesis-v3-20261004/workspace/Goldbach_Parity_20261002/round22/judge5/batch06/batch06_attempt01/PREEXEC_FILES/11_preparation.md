# Batch06 — audit SOURCE et préparation indépendante

ROLE5, nouveau lot dans `B/round22/judge5/batch06`,
`B=D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002`.
Statut SOURCE uniquement. Aucun Lean, probe, import/calcul numérique, installation
ou Git. Aucun ancien lot Juge/auteur rejoué. La compilation future exige sa
propre gate ROOT liant ce nouveau manifeste et ce nouveau lanceur.

## Sources concrètes et ordre

| Module | SHA256 | FULL original | Théorèmes + définitions |
|---|---|---|---|
| ZetaEulerDirect22 | 0d790ed67706e2f3c3556d2c5e7fefd50664177f5fb54584beee1d137e430a71 | 1145d0 | 4+1 |
| ZetaReflection22 | 54e32a95a62929c7251bf130156adbc7da7d66ceb1cb77609382e33c025f4a42 | 388201 | 6+1 |
| GammaPsiDuplication22 | 0491177c6cfc1ef35b28796be404a3ca7975bac357cc6551b80d12333726812e | 1748b3 | 2+0 |
| GammaPsiReflection22 | 8e070c18a483ac71703f66b80dbcf4129f0f16ada8f2a933497655b3a7cdaa30 | a8d62a | 5+0 |
| ContourChiPsi22 | a90d536187fe342d01cf913a56c80a34e6846eb273a533bcdd843289f7d83248 | b7ddba | 9+1 |
| ContourChiScaled22 | d0aa03290fe806f9c84c0311a7e07a2fe0737148c9c1de7c80876118fb7a64d7 | 56411a | 8+2 |
| PsiKernelEnvelope22 | 949c6fc0d895003b522518e18ae89bdf6b5062448d5273f146685645afb72ef8 | 1a045e | 8+1 |
| PsiKernelDomination22 | 80b85c14c7db79121f7c9cb003edf97a7d5e947f785ce8402f910ea93aad48bc | f4d66f | 19+2 |
| PsiMixedFubini22 | d143b0fbdf795a1b400f737274a5eae5c8c5bba0c2e4ecaf145d86932df0b250 | e4904c | 17+2 |

Total concret attendu 88 déclarations = 78 théorèmes + 10 définitions,
88 commandes qualifiées `#print axioms`. Le builder vérifie exactement cet
inventaire lexical, sans élaborer Lean. Les sources propres sont des copies
exactes vérifiées par 8b7eab. Elles ne contiennent pas de preuve modifiée.
Dup05 est le seul PASS auteur préalable de ce lot ; ses deux déclarations
restent à juger indépendamment. Les huit autres modules sont SOURCE non
compilée. Un import, une revue ou un futur `#print` ne leur accorde pas PASS.

## Audit mathématique concret

EulerDirect utilise la vraie fonction `riemannZeta`. La sommabilité des normes
pour Re(s)>1 et le produit Euler analytique générique construisent
`exp(sum prime logs)=zeta(s)`, puis sa non-annulation. Aucune inversion de
Möbius, aucun crible, aucune forme bilinéaire arithmétique n'est proposé.
La fermeture d'import cache est une liaison source/olean, pas une nouvelle
preuve indépendante de tous les théorèmes antérieurs de mathlib.

ZetaReflection utilise la vraie équation fonctionnelle en voisinage de la
bande −1<Re(s)<0. Γ, la puissance de 2π et le cosinus y sont non nuls ; la
réflexion ζ′/ζ est obtenue par différentiation du produit et division légitime.
L'absence de zéro dans cette bande ne compte pas les zéros critiques et ne
paie pas le passage des contours infinis.

Duplication et réflexion Γ sont différentiées sur des domaines positifs
pour les arguments Γ utilisés. Les exclusions de zéros des dénominateurs
Γ, sinus, s et puissance sont construites. Le logarithme de 2π est celui du
réel positif. χ′/χ est la dérivée logarithmique du `contourChi` effectif de ROLE4,
pas celui d'un objet de substitution. P1 apporte les deux intégrales Ψ et
leur intégrabilité déjà jugées. L'identité appariée conserve la cancellation
en u=0. `Scaled` transporte intégrabilité et Jacobien absolu 2 sous u=2v.
Son identité totalisée pour tout s ne remplace pas son théorème séparé
d'intégrabilité dans la bande ouverte.

Le numérateur N(t,v) s'annule en v=0. Sa dérivée est réellement bornée par
7+2|t| pour v≥0 ; la valeur moyenne donne (7+2|t|)v. Le dénominateur
1−exp(−2v) positif est minoré par 2v/(1+2v), puis v/2 près de zéro et
1/2 pour v≥1. Les bornes du vrai noyau donnent 14+4|t| et 8exp(−3v/2).
L'enveloppe E(t,v)=(14+4|t|)exp(1−v)+8exp(−3v/2) est explicitement
continue et intégrable sur v>0 ; aucune hypothèse de majorant libre.

MixedFubini utilise exactement `gammaContourFactor Y (-1/2) 1 t` fois ce
noyau. Γ(1/2+it) est bornée via sa récurrence vers Γ(3/2+it) et les
bornes Γ indépendantes : 4Y^(−1/2)exp(−π|t|/4), valable pour tout Y>0
sur cette droite exacte. Cela ne réutilise pas indûment le domaine Y≥1 du
majorant ΓContour de bande. L'intégrabilité produit de cette enveloppe
mixte est construite par deux produits Laplace, avec le facteur |t| payé.
La continuité du vrai intégrande sur v>0, la positivité du dénominateur et
`Measure.prod_restrict` paient sa mesurabilité pour la mesure produit.
La domination `mono'` établit alors sa vraie intégrabilité AVANT Fubini.
Le théorème final d'échange a seulement Y>0 comme prémisse ; le helper
générique `integrable_abs_extension` reçoit hf, construit dans tous ses
usages concrets. Ni Fubini, ni un majorant, ni la cible D_N ne sont supposés.

Cette lecture mathématique reste SOURCE, sans garantie d'élaboration des APIs.
Les noms/binders de MeanValue, `prod_mul`, `prod_restrict`, mesurabilité,
Jacobian et `integral_integral_swap` seront jugés seulement par la gate future.

## Provenance et dettes préservées

Revue C5 ancienne SHA b2458e4edfd3a8b21de91a09d2d3ea4a0134ae764dc64d7c1d617cdd3b0a66e8,
relue FULL53f668 ; revue enveloppes SHA6ac1af9df6b555aa34dcb9714c6c43f8dd6345d804577409688ca7ef3557cccc,
FULLdcdccb ; checkpoint C5 SHA9119650574a298e229f620623d50c14d7e749d915305ffe0fa459a9dc6c889f7,
FULL68ae01. Ces archives décrivent l'état historique 66/1109 et l'échec
ΓContour244f20 ; elles ne sont pas réécrites. La dépendance homonyme actuelle
est explicitement celle de batch05 corrigé891454, indépendamment PASS.
Dup05 reçu74b5dfe2… relu FULL90775a, FIN/log FULL1a9e6f.

Sept dépendances locales readonly, toutes indépendamment PASS : ΓPrereq,
ΓDerivative, ΓBox, ΓContour corrigé, P1Core/BetaLimit/Integral. Leurs sources,
oleans et reçus sont liés exactement ; aucun olean auteur sur LEAN_PATH.
P1 sources relues FULL4a0681/732f07/6060c8. Toutes les anciennes entrées Juge
et les 3089 archives restent protégées ; aucun ancien lot n'est recompilé.

Le futur lanceur aura au maximum neuf enfants séquentiels, arrêt au premier
échec, aucun retry/probe, dossier output neuf et captures PRE/POST/START/FIN.
Tous les 88 prints doivent couvrir les 88 déclarations et leurs axiomes standards
exactement ; `sorryAx`, axiome évaluateur, olean manquant ou erreur ferment le lot.

Ce paquet ne raccorde pas encore la vraie inversion Mellin à l'Arch original,
le transport x=exp(v), la normalisation/orientation, log2 et le −1 final C5.
Il ne certifie ni les budgets effectifs de quadrature/troncature, ni les
primitives intervalle, ni compte complet des zéros. H1/globalArch/C3/C5global,
coefficient N, D_N et WIN demeurent ouverts. Officiel ROOT : 68 modules /1132 avec
définitions ; potentiel 77/1220 uniquement si les neuf PASS réels sont observés.
