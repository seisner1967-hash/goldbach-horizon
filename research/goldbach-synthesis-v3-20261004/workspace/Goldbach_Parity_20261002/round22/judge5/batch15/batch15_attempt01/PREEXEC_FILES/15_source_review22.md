# Discrete29 révision03 — SOURCE uniquement

La révision02 a effectivement échoué devant le Juge14, exit1, du 2026-10-03T16:47:24.487228Z au 16:47:49.350927Z ; aucun olean. Le log complet 879f2978a6de8935608661b3194a36c728fbff743c864c3f114405fc463c3d0a et le FIN complet 1ef1a87c885aafa907c810a4a17f973923ea17755a5b4748c616616ccfc84104 ont été lus. Les sept sorryAx sont des récupérations d'élaboration, sans crédit de preuve.

Corrections limitées aux quatre blocages observés :

- Ancienne ligne92 : le rw de l'équivalence de divisibilité sous ite gardait un Decidable dépendant. Le rw de la somme est conservé, puis simp only utilise grid_divides_iff_zero et reconstruit la décision.
- Ancienne ligne114 : simp only [hz] transporte la condition entière/naturelle sous ite au lieu du rw rejeté.
- Ancienne ligne196 : push_cast normalise à la fois hc et le but, dont la division réelle et l'exponentielle différaient auparavant.
- Ancienne ligne285 : simpa only [Int.cast_neg] transporte le cast de -(N:Z) dans le caractère final.

Les 29 en-têtes, domaines, fonctions, poids vonMangoldt et 29 #print axioms restent identiques. L'expansion sum_mul_sum précédemment corrigée reste intacte. A0 impose max N (2*M-N)<K et N≤M ; aucune orthogonalité finale en prémisse. Il s'agit toujours de l'identité finie du cercle avec tous les premiers et puissances de premiers. Aucun résultat sur D_N ni WIN.

Cette source neuve n'a été ni compilée ni soumise à une sonde. Aucun ancien fichier ou ancien lot n'a été modifié. Le Juge et une gate ROOT distincte sont requis. Les normalisations proposées sont une correction SOURCE, sans PASS anticipé et sans diagnostic de parité.