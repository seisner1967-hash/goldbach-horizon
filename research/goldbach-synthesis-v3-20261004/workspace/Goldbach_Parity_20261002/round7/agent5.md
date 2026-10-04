# Agent 5 — Juge indépendant, boucle 7

2 octobre 2026. **Verdict du mécanisme soumis : REJECTED_BEFORE_COMPILATION. Victoire = false ; score sémantique = 0.** Les identités exactes de couverture et de caractères sont conservées. Le gain signé complet manque et le remplacement du facteur natif par le twist bipolaire est faux. Aucun fichier Lean de substitution n'a été produit, aucun compilateur invoqué, aucune erreur Lean fabriquée. Les acquis formels restent **neuf modules auxiliaires et 116 conclusions**, sans augmentation dans cette boucle.

## Rejeu indépendant reproductible

Commande PowerShell complète :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round7\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

L'audit a terminé avec **exit 0**, puis `Score: 0`. Il arrête toute étape dépendante si le rejeu Python renvoie un code non nul ; il ne traite pas un ancien reçu comme résultat de ce rejeu.

Les cinq rapports définitifs, les trois sources numériques, leurs JSON, les helpers et le registre sont figés dans `judge/input_sha256.json`. Le builder compare leurs SHA-256 avant et après. Le wrapper charge les scripts par leurs chemins originaux et dirige uniquement leurs sorties vers `judge/numerical`. Il charge explicitement le module de conservation de round7 avant les imports des helpers d'anciennes boucles, afin de vérifier le registre de **190** fichiers et non celui de round6. Les copies des scripts dans le dossier isolé sont conservées comme pièces de traçabilité.

Chaque objet JSON est comparé intégralement, sans supprimer de champ. Les octets et SHA-256 des trois sorties sont également identiques aux reçus originaux. Le statut propre à chaque banc reste inchangé :

| Banc | Statut du gate original et rejoué | Domaine fini constaté |
|---|---|---|
| `logarithmic.json` | PASS_IDENTITY_ONLY | 19999 entiers, 65533 termes de puissances premières ; préfixes X=303 et 1024 |
| `jacobi.json` | PASS_IDENTITIES_ONLY | Six premiers, 44944 préfixes centrés, cinq tuples HH, douze cellules CRT |
| `trace.json` | PASS_EXACT_CONNECTION_ONLY | 64 lignes natives, 7394 cas de la trace antérieure |

`PASS_EXACT_REPLAY` dans le reçu du wrapper qualifie uniquement la reproduction de ces trois gates distincts. Il ne transforme aucun d'eux en preuve du gain. Les **190/190 anciens artefacts** ont leurs empreintes inchangées avant et après ; les entrées originales de round7 sont également préservées. Les exclusions du registre — caches, état Arbor et rapport central vivant — restent explicites.

Les empreintes finales des trois JSON reproduits sont :

| JSON | SHA-256 original = isolé |
|---|---|
| logarithmic | `00f7d0faf027e3b8f31844e4af9042cc2983eaf34aff91994f85af56dbba40d9` |
| jacobi | `1874d65c4e3d224e03151719a3ed685b1c2127c6ac763c92f44e812bcee9bb13` |
| trace | `919e2d2ae72eadc6ccf713e42c041c5fbac522024f812682379e842f74f972e2` |

Le reçu principal fige les cinq rapports par leurs empreintes : Agent1 `309195a841c1da3dfeebde518def34c07cc781df240eea9f5a797be02d001b00`, Agent2 `ed04474b59e888696945838b11f0b15abcec6ad71d40f2d09db2e0cdf5ec7348`, Agent3 `74b18c1061dbe570f2a966a79f6ee13ac65219dc1285b84994599e3ecd0ccc76`, Agent4 `cfbd833206c0d8e838ef75b38dfe97d51c13d17ede0ac22fcda4ec91ad92babb`, Agent6 `e1c838ebd58c7fbd9107c26e7be28ca9b76cb1e01091fcae36bfa7be2f7b7757`. Le builder et le wrapper ont eux aussi leurs empreintes dans les reçus.

## Couverture complète et paiement analytique partiel

Le profil raw garde ses arguments véritables, unités, faces strictes et puissances premières du premier axe. Aucun masque μ(N−m)² n'est ajouté. La convolution standard

`μ(m)log m = −sum_(d|m) μ(m/d)Λ(d)`

fournit la couverture complète L1 pour m>1 ; F_N(1)=0 garde le dénominateur log m hors du cas zéro. La réduction L2 aux premiers est correcte **avec p∤ell**. Elle vient d'une cancellation exacte des puissances ; elle n'autorise pas la suppression de j≥2 dans L1 sans ce filtre. Les témoins actifs 841 et 10201 ont des coefficients −1/2,+1/2 qui s'annulent. Les 19999 comparaisons de coefficients et les insertions finies dans le profil reproduisent ces identités sans division logarithmique flottante.

La réparation de couverture de la boucle 6 est réelle : m=303 est couvert, et un premier comme m=311 reçoit le poids entier dans ell=1. Cela ne constitue pas une estimation du signé complet. Les secteurs ell=1 et premiers longs restent présents ; une nouvelle coupure p≤Y recréerait son défaut exact R_Y. Les préfixes numériques ne calculent pas leur extérieur. Les puissances premières propres sur n=N−m demeurent dans le raw, distinct de la composante HH filtrée.

Le paiement de queue Mellin L5 est un **résultat analytique écrit partiel**, accepté dans sa portée. Avec u=log N, ell=log u, l'enveloppe réelle antérieure et α≥exp(u/4), le choix

`B=1024 sqrt(20) u³(1+u)^(3/2) ell`, `T=(4/u)log B`, pour u>1 et B>1,

donne `|integral_T^infinity A(t)dt| ≤ N/(1024u ell)`. La simplification des constantes utilise un majorant absolu indépendant et n'assume pas la cible. A(t)=S′(t) reste la dérivée du moment original. La partie 0≤t<T, où les grands premiers du secteur ell=1 gardent presque tout leur poids, n'est pas payée. Ce résultat n'est **pas certifié Lean** et le test numérique ne prouve pas son domaine analytique.

L'audit 3 justifie le minorant écrit **C1≥N log N/384 éventuellement pour N pair, 3∤N**, en conservant le vrai endpoint quartique, le masque polynomial de Lemma 10.1, la contribution des grands premiers unitaires et le coût du petit secteur. Le PNT aux deux classes réduites modulo 3 intervient à module fixe. Le seuil global n'est pas évalué ; ce résultat ne vaut pas par le présent audit dès u=1024 ou à N=10^8, et aucune intrinsèque inefficacité du PNT fixe n'est alléguée. Il n'y a aucune certification Lean nouvelle de ce minorant.

Le raccord demeure `D_N=C1−S_rest+2max(e,0)`. Le minorant interdit, éventuellement sur cette sous-famille, de payer C1 séparément comme petite erreur absolue au budget demandé. Il ne réfute pas une compensation signée future par S_rest. Ni une identité standard ni le paiement de la queue Mellin ne prouvent cette compensation ; la prendre comme hypothèse du futur théorème serait circulaire.

## Caractères : normalisation, exceptions et raccord réel

Pour p∤N, la partition du porteur physique en Omega_p et R_p est exacte. La reconstruction principale par les p−2 caractères nonprincipaux conserve tous les facteurs de caractères, les quatre valeurs de Möbius et les exceptions p|n ou p|m. Le centré garde séparément son modèle :

`E_HH=R_p−sum_(chi nonprincipal)conjχ(−1)Tχ−M_HH`.

L'identification de C_HH au poids physique doit conserver sa normalisation originale ; aucune insertion automatique dans M_HH ou les corrections W n'est acquise.

Le Jacobi complet vaut exactement `sum_ζ χ(N−Cζ)conjχ(Cζ)=−χ(−1)` pour p∤NC. Omettre conjχ(C) change sa phase en −χ(−C). Cette moyenne est non nulle, et la reconstruction de l'ensemble des modes redonne **p−2**, la masse principale. La formule jointe centrée retrouve la discrepancy de deux résidus exclus, bornée par 2 sur une progression de pas unitaire modulo p. Ce faible coût est **par cellule**, avant paiement des poids à variation réelle, de la multiplicité extérieure, des queues et des exceptions. Les pentes divisibles par p sont conservées comme phases fixes ; la borne de préfixe ≤2 ne leur est pas attribuée.

**La précision de l'audit 4 est correcte et nécessaire :** pour A=273 et C=10403, les sommes complètes aux premiers **3,7,13** sont des diagnostics de normalisation sans le masque A. Ces p divisent A ; la vraie composante p-unitaire de cette fibre est vide. Ils ne sont pas des cycles admissibles de la fibre HH. Le diagnostic CRT **p=11, M=819** est admissible dans son domaine de cellules signées ; ses douze points e=3 ne sont pas douze tuples HH carrés-libres. Le CRT général et ses lcm, tests de compatibilité avant inversion, exceptions, secteurs ζ=1 et +1 sont conservés.

Le raccord natif utilise **conjχ(N)**, tandis que le nouveau twist utilise **conjχ(m)**. Le vrai tuple

`b=101,u=103,v=107,x=43,k=7,s=3,t=71,ζ=34967`,
`n=47864203,m=52135797,a=473903,r=7447971`

conserve les fronts, unités N, carrés-libres et quatre signes (produit +1). Modulo 7, m est nonunité ; tous les nouveaux twists valent zéro et R7 porte ce secteur. La ligne native vaut pourtant **5/6**. Le remplacement de cette ligne par le twist bipolaire est donc arithmétiquement faux, avant toute tentative Lean. De même, un conducteur choisi dans a*r rencontre au moins un axe nonunitaire du tuple ; il ne devient pas un twist fixe non dégénéré sur toute une famille par simple choix tuple par tuple.

La trace primitive antérieure est conservée dans son domaine carré-libre. Sur gcd(q,m)=1, `μ(q)P_q(m)/φ(q)=1/φ(q)` ne fournit pas deux oscillateurs indépendants. Le diagnostic q=9 rappelle seulement qu'il ne faut pas étendre le domaine au q non carré-libre. Aucun nouveau résultat de trace signé n'est revendiqué.

## Décision du Juge

| Proposition évaluée | Classification | Portée |
|---|---|---|
| Couverture complète L1/L2 avec ses supports | EXACT_IDENTITY_RETAINED | Réparation arithmétique réelle, sans estimation signée |
| Queue Mellin L5 | ANALYTICAL_PARTIAL | Budget écrit indépendant ; proche de t=0 ouvert ; aucune preuve Lean |
| Minorant du secteur C1 | QUALITATIVE_EVENTUAL_PARTIAL | N pair, 3∤N ; seuil non évalué ; aucune preuve Lean |
| Supprimer ell=1 ou les puissances sans leur cancellation | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | Témoins raw actifs, coefficients exacts |
| Payer C1 seul au budget terminal | SHORTCUT_REJECTED_EVENTUALLY_ON_STATED_SUBFAMILY | Le minorant qualitatif est trop grand ; la compensation reste possible |
| Insertion N1–N9 avec modèle et exceptions | EXACT_IDENTITY_RETAINED | Tous les modes reconstruisent la masse principale |
| Petites sommes complètes de Jacobi ⇒ gain HH complet | SIGNED_GAIN_NOT_OBTAINED | Cumul extérieur, poids et R_p non payés |
| Nouveau twist bipolaire remplace la ligne native | SHORTCUT_FALSIFIED_BEFORE_COMPILATION | Tuple k=7 : zéro contre 5/6 |
| Cycles p=3,7,13 avec A=273 crédités à la fibre p-unitaire | INVALID_TRANSFER | Diagnostics non masqués ; fibre physique vide |
| Erreur Lean nouvelle | NONE_OBSERVED | Aucun compiler ni nouveau .lean |
| Condition de victoire | NOT_MET | Aucun contournement quantitatif du signé complet certifié Lean |

Le rejet vise ces transferts et paiements précis. Les couvertures complètes, les regroupements signés et les mécanismes généraux de caractères restent des pistes ouvertes lorsqu'ils conservent leur vraie comptabilité. Les documents des autres rôles et l'état Arbor n'ont pas été modifiés.
