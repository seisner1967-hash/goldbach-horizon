# Batch04 indépendant — Core Ψ seulement

SOURCE préparé, aucune compilation avant gate distincte. Module unique
GammaPsiCore22, source450962be9526866fa0ffebc39ef29a819d94b57a90000291337550e9f4dc7284.
Catalogue :15théorèmes et4définitions,19prints qualifiés. Copie exacte immuable,
aucune preuve écrite ou réparée par le Juge. Le reçu auteur global
AUTHOR_PSI_BATCH_FAILED concerne le module BetaLimit suivant ; la première ligne
Core est AUTHOR_LEAN_AUX_PASS, exit0,19axiomes standards, olean réel.
BetaLimit, Integral et Duplication sont exclus ; aucun retry ni ancien replay.

Les objets sont la vraie Γ et gammaPsi(z)=Γ′(z)/Γ(z), le quotient
Γ(z)Γ(1+w)/Γ(z+w), le pas positif1/(n+1), et l'intégrande bêta de différence.
Pour Re z>0, la preuve construit la différentiabilité de Γ, la dérivée de sa
récurrence via égalité de voisinage, Ψ(z+1)=Ψ(z)+1/z et Ψ(1)=−γ_E.
Le quotient est dérivé à w=0 avec les vraies dérivées de Γ et sa non-annulation.
Pour w>0, la vraie formule bêta de mathlib identifie le quotient à w B(z,w),
puis les différences bêta au quotient de différences. Le slope derivative et
le pas1/(n+1) établissent la limite des valeurs d'intégrales vers−γ_E−Ψ(z).
L'égalité avec l'intégrale de différence pour chaque w>0 paie son intégrabilité
par betaIntegral_convergent ; elle n'assume aucune domination ou convergence.

Le premier déficit aval reste le passage w→0 sous l'intégrale : le majorant
intégrable uniforme et DCT à l'extrémité sont distincts de la limite des valeurs.
Core ne prouve ni formule intégrale Ψ au paramètre zéro, ni échange Fubini/Arch,
ni C5, identité Weil, déplacement infini de contours ou coefficient Goldbach.
Il n'a aucune dépendance locale ; LEAN_PATH contient uniquement sa sortie neuve
et les huit caches mathlib existants. Les anciens batches Juge01/02/03 sont liés
readonly, sans recomposition ni recompilation.

Python fixé4278cf… avec -B -X utf8, Lean4.15.0 fixé8a1ef185… ; mathlib
9837ca9d65d9de6fad1ef4381750ca688774e608. Chaque import est lié à sa source et
son olean, fermeture Init explicite. Sources auteurs/reçus/log lus FULL ; API bêta
lue TARGETED. La fermeture complète est parsée et liée en SHA, sans revendication
FULL mathématique des bibliothèques ou des grands JSON. Aucun banc numérique requis.

Lanceur neuf, gate ROOT exacte, tentative unique batch04_attempt01, un seul enfant.
Il écrit PRE/captures, START global/module, commande/stdout/stderr, FIN, POST/receipt.
19prints doivent correspondre exactement au catalogue, axiomes seulement propext,
Classical.choice et Quot.sound, aucun sorryAx/native_decide/unsafe. Les3089 archives
et tous anciens fichiers Juge restent inchangés. Les helpers repris sont du texte
SOURCE copié ; aucun ancien builder ou lanceur n'est exécuté/importé.

Base indépendante précédente :63modules/1057auxiliaires après le vrai Γ′ ; le
compteur officiel dépend de l'observation ROOT. Delta éventuel Core :1module et
19déclarations (15théorèmes,4définitions), soit64/1076 après véritable audit PASS
et observation. H1, C3/C5, D_N et WIN ne sont pas acquis.
