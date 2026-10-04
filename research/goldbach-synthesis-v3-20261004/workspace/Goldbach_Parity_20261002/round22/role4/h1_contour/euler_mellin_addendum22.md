# ROLE4 — Euler direct, Λ et les deux échanges de Mellin

Statut : SOURCE ONLY, non PREPARED, non compilé. Ces fichiers prolongent les
28 déclarations initiales H1 sans modifier leurs sources ou reçus. Aucune
invocation Lean, probe/version, opération mathématique Python ou banc nouveau
n'a eu lieu ici. Le contrôle lexical ne constitue pas une validation Lean.

Les quatre nouvelles sources contiennent 55 déclarations et 55 futurs audits
qualifiés, soit 83 déclarations H1 en source avec le premier paquet. Elles
n'utilisent aucune prémisse libre de trace, Λ, Mellin ou Fubini.

| Source | Déclarations | SHA256 |
|---|---:|---|
| ZetaEulerDerivative22.lean | 14 | fe51d8956fecabaa09063ce31543b91946cc3fae1fd2e3ffadd4fc639be39520 |
| ZetaEulerLambda22.lean | 14 | 1a08c2258a3e544b7e9e643de2be9f03bddcff90822592dbbca08c53871d5266 |
| MellinLambdaInterchange22.lean | 13 | 95eb68ee1ae56d8cede154a04587535021e916ea73b4bed12ef6883cc0a12803 |
| MellinDualLambdaInterchange22.lean | 14 | 5f63a74bfcca27c588f2ed53f22130b3a617c1cca778cd161bc6cb96e9ff3182 |

## Charges réellement écrites

Le logarithme du vrai produit d'Euler est différentié sur Re(s)>1. Pour une
demi-droite locale Re(z)≥κ>1, la norme de la dérivée du facteur premier est
majorée par (2/δ)p^(-a), δ=(κ−1)/2 et a=(κ+1)/2>1. Les conditions de branche
de log(1−p^(-s)), sa norme ≤1/2, le dénominateur ≥1/2 et la convergence de la
p-série sont construits ; ils ne sont pas des hypothèses du théorème final.

Le poids Λ_direct(n) vaut log(minFac n) pour une puissance première, zéro
sinon. Le majorant Λ_direct(n)≤log n et log n≤n^δ/δ établit la convergence
absolue de ΣΛ_direct(n)n^(-s). La bijection canonique du cache
Nat.Primes.prodNatEquiv envoie (p,k) sur p^(k+1), avec inverse par minFac et
factorisation. Cette preuve utilise l'unicité des puissances premières et une
série géométrique analytique ; aucune inversion ou convolution arithmétique
n'entre dans la chaîne sélectionnée. Le résultat écrit est réellement

    ζ′(s)/ζ(s) = −Σ_(n≥0) Λ_direct(n)n^(-s),   Re(s)>1.

Sur la verticale, la norme de Λ_direct(n)n^(-s) est constante en Im(s).
Chaque intégrande est dominé par cette norme multipliée par |G(s)| ; leur
somme est dominée par Σ|Λ_direct(n)n^(-Re(s))|·|G(s)|, une fonction intégrable
construite à partir de l'intégrabilité Γ et de la convergence absolue réelle.
La mesurabilité de la somme est obtenue comme limite des sommes finies.
Le théorème d'échange somme/intégrale reçoit donc ses vraies conditions.

Avec α=1/(2π), G(s)=Y^s Γ(s+1) et Y≥1, les deux conclusions écrites sont :

    α∫_(t∈R) G(c+it)(−ζ′/ζ)(c+it) dt
      = Σ Λ_direct(n) f_Y(n),                  1<c≤3/2,

    α∫_(t∈R) G(d+it)(−ζ′/ζ)(1−d−it) dt
      = Σ Λ_direct(n) f_Y(1/n)/n,              −1/2≤d<0.

Les termes n=0 sont nuls par le poids direct. Pour n>0, le passage réciproque
utilise arg(n)=0, la formule exacte inv_cpow et l'identité
n^(-(1−s))=n^(-1)(n^(-1))^(-s). Le facteur supplémentaire 1/n est conservé.
L'inversion Mellin porte sur le vrai test thermique, déjà écrit en source.

## Révision d'API distincte

La copie gamma_revision01/GammaContourComponent22.lean conserve ses onze
déclarations et son intégrande Γ réel. Son SHA est
9124b02b9d136b60b87cd6b2c01e6bac03e0fd8fef766cdfe97a79135a00aa44.
Le seul changement remplace integral_const_mul par l'API vérifiée
MeasureTheory.integral_mul_left dans l'intégrale globale. L'original
084a19087d9d9adabe7921d509cd8b8fce2d721be445bcb779a3555f264e5bf8
reste intact. Il s'agit d'une correction anticipée par lecture du cache,
pas d'un échec Lean inventé. Un futur staging doit sélectionner cette copie
pour le nom de module GammaContourComponent22 ; elle n'a pas été compilée.

## Dépendances et dettes restantes

Le module Γ final 9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7
a reçu auteur PASS puis Juge indépendant PASS. Le reçu indépendant batch02
annoncé et vérifié par ROOT est a159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9.
Cette dépendance est acquise sans nouveau rejeu. Les modules Γ′, boîtes,
Γ-contour et Mellin restent SOURCE ; leur présence comme imports ne leur
attribue aucun PASS ni aucune continuité validée par le compilateur.

Le raccord arithmétique ci-dessus ne ferme pas C3/C4 : il faut encore payer
la contribution rationnelle 1/(s−1), l'intégrale réelle χ′/χ, la vraie formule
Ψ/C5 avec Fubini et constantes, et le raccord au vrai A(s)=(s−1)ζ(s) avec
valeur amovible en1. Les résidus du rectangle C7, la certification des zéros
et du bord, les queues uniformes C6 et C8 ainsi que le contrat numérique H1
restent distincts. L'étape additive N et la cible D_N ne sont pas établies.
Ce paquet ne constitue ni une victoire ni une preuve de franchissement du
mur de la parité.

Lectures complètes des nouvelles sources : EulerDerivative 324a0e,
EulerLambda ece6be, MellinLambda 38d5b2, MellinDual 045bbd ; copie Γ602108.
Le premier essai purement documentaire 5bd546 a échoué avant exécution
à l'analyse PowerShell (pipe après foreach), corrigé en045bbd. Aucun calcul
mathématique ou invocateur Lean n'était dans cette commande.
