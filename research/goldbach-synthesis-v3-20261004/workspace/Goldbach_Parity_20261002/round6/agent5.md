# Agent 5 — audit indépendant de la boucle 6

2 octobre 2026. **Verdict : REJECTED_BEFORE_COMPILATION pour les raccourcis faux ; identité finie corrigée conservée ; victoire = false ; score = 0.** Aucun nouveau fichier Lean ni appel au compilateur dans cette boucle. Le compteur historique reste **9 modules et 116 conclusions auxiliaires**, déjà jugés dans les boucles précédentes. Le score zéro mesure l'absence du mécanisme quantitatif demandé, pas un échec du rejeu numérique.

## Reproduction et conservation

Commande complète, depuis PowerShell :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round6\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

Le script a terminé avec **exit 0**. Il lit les quatre rapports finaux et le rapport numérique par leurs empreintes, vérifie le manifeste antérieur, puis rejoue les deux scripts originaux en dirigeant uniquement leurs sorties vers `round6/judge/numerical`. Les JSON sont comparés intégralement : aucun champ, temps, coefficient ou statut n'est exclu. Leurs octets donnent aussi les mêmes SHA-256 que les reçus originaux. Les copies locales des scripts servent à la traçabilité ; les fonctions rejouées proviennent des scripts figés, avec leur vrai `__file__`.

| Gate | Statut conservé | Résultat indépendant |
|---|---|---|
| `katai.json` | PASS | Tous les champs et SHA-256 identiques |
| `squarefree.json` | PASS_CORRECTED_CONTRACT | Tous les champs et SHA-256 identiques |
| Manifeste des anciens fichiers | PRESERVED | 160/160 avant et après |
| Sources et reçus originaux de la boucle 6 | PRESERVED | Empreintes avant/après identiques |

Les comptes CRT finaux sont **1066 cas**, **558 cellules compatibles**, **23544 cellules signées brutes** et 5 cas actifs dans les domaines explicitement listés. Ils proviennent du JSON rejoué. Le long intervalle contient 19 points de congruence, dont 2 conservent les masques HH originaux. Aucun de ces domaines n'énumère la somme complète sur N.

Les SHA-256 finaux du rapport 3 (`2febcc018e728cf704c56de2f6225791e13fcfb86c81b44267c529a297aa615f`), du rapport 4 (`e35fc356c3f6ca0c2d906d1b97158b0ec12c904f6de28673f2f5692441033633`) et du rapport 6 (`a7cc44fec1da5a96171b2f9a873055e43121dc8bd43d697be4341066ca7ff399`) correspondent aux notifications de gel. Les tableaux d'empreintes numériques historiques du rapport 3 précèdent les ajouts finaux ; ils ne servent pas de gate actuel. `judge_receipt.json` contient les empreintes actuelles des scripts et reçus, ainsi que le manifeste et les traces de rejeu.

## Portée arithmétique vérifiée

Le profil brut conserve les faces strictes et le masque rho1, sans ajouter μ(N−m)². Le témoin **n = 9967² = 99341089, m = 658911** donne μ(m) = 1, μ(n)² = 0 et une contribution brute strictement positive, certifiée par intervalles rationnels de logarithmes. Un masque carré-libre supplémentaire changerait donc l'objet étudié. Le profil brut au premier m = 311 et le porteur HH ne sont pas identifiés ; le vrai tuple HH `(21,13,99999727,1)` est aussi conservé avec porteur 4 et couverture nulle par `{3,7,11,13}`.

L'identité Kátai finie **a_X S_X = −T_X + R_X** est correcte avec exclusions p∤m, normalisation par les planchers, diagonales de Gram et résidu de couverture. Pour **X = 303, P = {2,5}**, les dilatations disparaissent par le masque unité, mais

`S303 = −log(99999697) log(101)/2 < 0`, `a303 = 211/303`, `R303 = a303 S303 ≠ 0`.

Ce témoin réfute le transfert qui supprime R_X. Il ne réfute ni l'identité exacte, ni Kátai avec son résidu, ni une future partition correcte. La fin du domaine, **99 999 696 arguments** dans ce préfixe, reste non calculée. Le raccord au bridge fixé est

`D_N = (T_X − R_X)/a_X − S_tail + 2 max(e,0)`.

Aucun terme de ce raccord n'est remplacé par une hypothèse de petites corrélations. La calibration BSZ inchangée discutée dans les rapports ne donne pas de premiers dans la fenêtre proposée à N = 10^8 ; ce diagnostic porte sur cette calibration et ne constitue pas un théorème d'impossibilité pour toute partition.

L'expansion à deux carrés S2 conserve les coefficients signés avant regroupement et les masques originaux. Dans la fibre `A x + C ζ = N`, les conditions structurelles incluent explicitement **gcd(A,C) = gcd(A,N) = gcd(C,N) = 1**. L'ancien S3 ne suffit pas à garantir une inversion : avec **A = 273, C = 10403, d = ell = 11, e = f = 1**, le coefficient et le module ont un pgcd 11 qui ne divise pas N. La cellule est vide et le script ne tente aucun inverse.

Le CRT général utilise désormais **L = lcm(d²,f)**, **M = lcm(A,e²,ell)** et **g = gcd(C L,M)**. Si g∤N, la cellule est vide. Sinon il réduit modulo M/g avant inversion et garde le cas M/g = 1. Le témoin d = f = 3 certifie L = 9 et invalide le produit 27 hors du contrat copremier. Dans le contrat corrigé **S3′**, gcd(d,f) = 1 permet L = f d², et **gcd(d,ell) = 1** reste nécessaire pour la conclusion d'inversibilité. Le cas e = 3 partageant A exige le lcm 819 : 12 points sont présents, contre seulement 4 avec le module produit 2457.

Les exclusions dans l'expansion sont des regroupements signés ; elles ne sont pas des suppressions termwise avant prise de valeur absolue. En particulier, f partageant 5 est omis seulement dans l'identité tordue, où χ5(ζ) = 0. Le script teste ce contrat corrigé, sans prétendre préserver l'identité non tordue après cette omission.

Sur les unités avec q | N, le produit complet

`χ(A)χ(x) conjχ(C)conjχ(ζ) = χ(n)conjχ(m) = χ(−1)`

est constant. Dans les deux points HH réels de la longue fenêtre, le caractère isolé de ζ varie, tandis que le produit complet vaut +1 pour l'ordre 2 et −1 pour l'ordre 4. Un gain oscillatoire du facteur isolé ne se transfère donc pas au produit physique sans traiter son compensateur.

Enfin, **ζ = 1** n'est pas jeté. La fibre réelle **A = 1113121, C = 213, ζ = 244769, x = 43** possède un point, alors que `N/(A C) = 100000000/237094773 < 1`. Son intervalle brut dépasse sqrt(N), mais sa congruence n'admet qu'un point. Le **+1** du comptage est indispensable ; une grande longueur brute ne fournit pas automatiquement une longue progression utile à Pólya–Vinogradov. Les queues et coûts décrits dans les rapports restent à majorer avec leurs masques et leurs termes de comptage.

## Classification des échecs

| Proposition | Verdict | Motif |
|---|---|---|
| Kátai fini avec R_X, diagonales et domaine extérieur | IDENTITY_NOT_FALSIFIED | Identité exacte conservée et rejouée |
| S2 et CRT général/corrigé | IDENTITY_NOT_FALSIFIED | Compatibilité et lcm exacts conservés |
| Corrélations nulles ⇒ gain après omission de R_X | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | Préfixe X = 303, R_X non nul |
| Masque μ(n)² ajouté au profil brut | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | Puissance première active 9967² |
| S3 initial ⇒ inverse inconditionnel | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | Cellules vides avec g∤N |
| lcm remplacé par produit hors coprimalité | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | d = f = 3 ; e partage A |
| Annulation du caractère isolé ⇒ annulation du produit HH | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | Compensateur complet constant |
| Comptage N/(A C) sans +1 | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | Fibre mince originale non vide |
| Contrôle quantitatif du signé complet / cible D_N | NOT_OBTAINED | Résidu, extérieur, diagonales, queues et compensateurs non bornés au coût demandé |
| Erreur du compilateur Lean dans cette boucle | NONE_OBSERVED | Aucun appel au compilateur, aucun nouveau .lean |

Ce gate constitue un audit arithmétique préalable et un rejeu numérique exact sur les domaines déclarés. Il ne constitue **aucune certification Lean nouvelle** et ne permet aucun rapport de victoire. Les identités corrigées restent candidates pour la recherche ; les déductions favorables falsifiées sont rejetées avant formalisation.
