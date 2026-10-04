# Juge indépendant — batch03, Γ′ auxiliaire

Statut initial : SOURCE préparé, gate fermée. Une seule source auteur est admise :
GammaDerivative22, SHA026ced6097c7d658b41501254bfbcdefe86ff2e68fb9fbe3fab01023a4cb0975.
Elle porte exactement huit théorèmes, aucune définition, huit commandes qualifiées
`#print axioms`. Aucune modification de preuve. Le commentaire historique
SOURCE_ONLY reste conservé dans la copie exacte ; le reçu auteur atteste sa
compilation ultérieure. Le statut global AUTHOR_ANALYTIC_BATCH_FAIL est dû au
module suivant ΓBox, tandis que la ligne ΓDerivative est exit0/olean/8prints.
ΓBox et les trois modules NONINVOQUÉS, ainsi que ψ, sont exclus de ce lot.

Le vrai théorème final porte sur `deriv Complex.Gamma s` avec
1 ≤ Re s ≤ 2 et donne ‖Γ′(s)‖ ≤ 19 exp(−π|Im s|/4). La preuve borne la vraie Γ
sur 1/2 ≤ Re w ≤ 5/2 par (27/5) exp(−π|Im w|/4), en utilisant la rotation de
Γ du module ΓPrerequisites22 déjà PASS indépendant. Le majorant de Γ réelle
≤9/5 utilise convexité et récurrence ; le coefficient angulaire est ≤3.
La conjugaison traite les hauteurs négatives. Une sphère de rayon1/2 autour de
s reste dans cette bande ; |Im w−Im s|≤1/2 et exp(π/8)≤7/4 donnent un majorant
189/20 pour Γ sur la sphère, avec le même facteur exponentiel au centre.
La vraie différentiabilité de Γ dans Re>0 assure DiffContOnCl sur la boule.
L'estimation de Cauchy de mathlib divise par le rayon1/2, soit189/10≤19.
Aucun majorant de Γ, identité de Laplace, intégrabilité, dérivée ou conclusion
cible n'est fourni comme hypothèse gratuite du théorème final. Cette inspection
SOURCE ne remplace pas l'audit du noyau Lean, encore fermé avant gate.

La seule dépendance locale est ΓPrerequisites22, source9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7,
olean indépendantfc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477
du propre batch02_attempt01 du Juge, en lecture seule. Aucun olean auteur ne
figure dans LEAN_PATH. Les anciens lots Juge01/02 sont clos ; les fichiers sont
liés par SHA, jamais recompilés. Les3089 archives antérieures sont conservées.

Python fixé4278cf… avec -B -X utf8 ; Lean4.15.0 fixé8a1ef185… ; mathlib commit
9837ca9d65d9de6fad1ef4381750ca688774e608, huit caches de packages existants.
La fermeture récursive lie source et olean de chaque import, avec Init ajouté
explicitement comme prélude implicite. Les bibliothèques sont lues pour leurs
imports et SHA ; aucun FULL mathématique de toute cette fermeture n'est revendiqué.
L'API Cauchy de Liouville est lue en extrait ciblé, scope TARGETED.

R01 componentiel est clos AUX_PASS46cas/19mutations. Ses reçus, contrat et
rapport de clôture sont lus FULL ; son résultat est parsé pour le statut et lié
par SHA, sans lecture brute FULL ni calcul de référence. Il ne constitue ni
oracle global ni prémisse de la preuve Γ′. Aucun replay, test numérique ou
checker n'est exécuté. Le contrat historique SOURCE_ONLY est conservé ; les
reçus réels ultérieurs déterminent le statut observé.

Le lanceur neuf exige une gate ROOT distincte liée au manifeste, au lanceur,
au reçu de préparation et aux runtimes. Tentative unique batch03_attempt01,
un enfant au maximum, sans probe, retry, installation ou git. Il écrit captures,
PREEXEC, START global/module, commande réelle, stdout/stderr, FIN module/global,
POSTEXEC et receipt dans son nouveau dossier. Les huit prints doivent couvrir
exactement le catalogue et ne dépendre que de propext, Classical.choice et
Quot.sound. Toute erreur ou conservation défaillante ferme le lot sans crédit.

Officiel avant observation ROOT :62modules/1049déclarations auxiliaires.
Si et seulement si ce nouvel audit passe, le delta proposé sera1module/8théorèmes,
soit63/1057. Aucun crédit H1, C3, C5, trace globale, coefficientN, D_N ou WIN.

