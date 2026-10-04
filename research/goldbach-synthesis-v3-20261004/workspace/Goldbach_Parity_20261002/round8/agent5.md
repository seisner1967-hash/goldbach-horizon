# Agent 5 — Juge indépendant, boucle 8

2 octobre 2026. **Verdict : PARTIAL_HEAD_GAIN_WITH_OPEN_SIGNED_REMAINDER ; victoire = false ; score sémantique = 0.** La tête physique bénéficie d'un gain analytique écrit indépendant, sous les inputs conservés, avec calibration BV supplémentaire non évaluée. Le complément signé de R16 reste ouvert. La candidature de Gram natif est classée `REJECTED_BEFORE_COMPILATION_MISSING_WEIGHTED_ARITHMETIC_ESTIMATE`. Aucun nouveau .lean de substitution, aucun appel au compilateur et aucune erreur Lean fictive. Le compteur historique demeure **neuf modules auxiliaires, 116 conclusions**.

## Gel et rejeu indépendant

Les rapports définitifs 1, 2, 4 et 6 ont été lus, puis l'audit 3 R1–R16 a été lu intégralement. Le gel a attendu le rapport 3 complet et son état **completed** dans le registre des agents. Son SHA-256 final est `ba35b03bfad822561168b5a1f80fd629035958f703ef232a4d2df06a07afe49c`. Aucun brouillon numérique n'a servi de gate définitif.

Commande complète de reproduction :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round8\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

Résultat : **exit 0**, puis `Score: 0`. Une étape dépendante s'arrête sur un code de rejeu non nul. Le builder ne valide pas un ancien reçu à la place de l'exécution présente.

`judge/input_sha256.json` fige les **cinq rapports**, les **trois scripts**, les helpers, les gates, le registre, la clarification de source, son renderer, ses rendus et le PDF original. Le wrapper charge conservation/shared par les chemins de round8 pour éviter les modules homonymes antérieurs. Il exécute les sources figées avec leur `--output-dir`, leurs véritables chemins et le registre original, en écrivant exclusivement dans `judge/numerical`.

Tous les champs des JSON sont égaux, sans exclusion. Les octets donnent aussi les mêmes SHA-256 ; les trois statuts distincts sont conservés :

| Banc | Statut original et rejoué | Domaine exact vérifié |
|---|---|---|
| compensation | PASS_EXACT_IDENTITIES_ONLY | Deux préfixes, cinq arguments isolés ; 65536 couples de bascule ; 1408 emplacements k |
| native_gram | PASS_ALGEBRA_ONLY | 9339 entrées premières ; 6120 entrées CRT ; mineurs raw et L2 |
| head_regrouping | PASS_HEAD_IDENTITY_ONLY | Douze m sélectionnés ; fibres complètes/coupées ; coupes avec queue |

Les **227/227 anciens artefacts** sont préservés avant et après, registre `b973b6ea8ce1fdef2a704e1e0bcc977ee7ac5b140e71d17cc3d90c165317243a`. Les entrées originales de round8 et le PDF sont également inchangés. L'état Arbor et les rapports des autres rôles n'ont pas été modifiés.

Les trois SHA-256 JSON reproduits sont respectivement `44fb25267eb3088037ef6d16bb3998a42a94952576662f279c35527aa702364c`, `ac4a14ae8a58a1579c16d84dd70aeac97e610b62b61514ff176e8bd0b8676ed0` et `f85071f0d1f6f1ecfd1d9612caf8d874bd9669933fd47fc00ae9ffffbc3cd7eb`. Les empreintes complètes des cinq rapports et des trois sources sont dans le manifeste et le reçu principal ; celles des scripts du Juge sont également liées au reçu.

## Source visuelle du domaine analytique

Les trois pages physiques ont été examinées directement. La page **32**, équation (66), affiche **u ≥ 10²⁴** ; la page **33** affiche **u0 = 10²⁴**, u0 < 2^80 et 54 < ell0 < 56 ; la page **36**, équation (72), répète **u ≥ 10²⁴**. Il ne s'agit pas de 1024.

Le Juge a aussi reproduit ces pages depuis le PDF original dans `judge/source_pages`, avec pypdfium2 au même facteur 1,7 et les textes pypdf. Les **trois PNG, trois textes et le reçu complet** ont exactement les empreintes des rendus canoniques. Le PDF inchangé a SHA-256 `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24` ; le reçu reproduit et original a SHA-256 `8b2997f16b1e705e619b664061abe4335fa820c43fb49a0e298895cc4e653662`. `SOURCE_ONSET_CLARIFICATION.md` et le reçu sont ainsi liés aux pixels et à cette source.

Cette correction explicite de lecture conserve les inputs acquis dans leur domaine original et leurs prémisses. Elle ne réécrit aucune ancienne archive. Les constantes budgétaires **1024** et les préfixes **X = 1024** restent légitimes. **N = 10^8** est un banc fini sous l'onset ; il ne valide aucun paiement analytique de cette monographie.

## Audit de la tête physique R1–R16

Le I de R1 est bien le Type-I acquis : même log n, masque unitaire, D−W et faces. L'identité `S_full=S_Lambda−I`, puis `D_N=−S_Lambda+I+2max(e,0)`, conserve le bridge et ses puissances premières unitaires. Le paiement global de I reste celui du §12.7 avec ses prémisses ; il n'est ni recomputé à N=10^8, ni affecté à chaque morceau, ni ajouté deux fois. Aucun μ(n)² n'est introduit dans le raw.

La bascule conserve la coprimalité : `μ(k)μ(kr)=μ(k)²μ(r)1_(k,r)=1`. Le front n>1 devient kr≤N−2, et le signe physique est négatif dans S_Lambda. **P1=M1** s'annule dans les deux branches avant les normes. Ce k=1 n'est pas le ell=1 de la couverture logarithmique de boucle 7. Après son retrait conjoint, le modèle est précisément M^{>=2} ; le paiement d'un modèle complet ne lui est pas transporté sans raccord.

R5 garde **gcd(d,rN)=1**, t|rad(r) et le vrai plancher. Son AP est bien `n=N−qv`, q=r d²t, jusqu'à N−1, avec qv≤N−2. Le regroupement R7 est bijectif sur ses coefficients non nuls : b=d t, c=r/t, g=t, q=b²c, r=cg, d=b/g. Il conserve b,c carrés-libres, gcd(b,c)=gcd(bc,N)=1 et **alpha<cg≤H**. La formule divisorielle complète ne s'applique qu'aux fibres complètes. **B_cut=floor(N^(1/32))** reste distinct du B acquis ailleurs.

Les queues R8 et R9 paient des objets distincts : la vraie queue physique et celle du principal AP infini. Le comptage sans +1 est valide seulement pour le préfixe spécial de **multiples positifs** N−qv ; les +1 des autres AP et fibres demeurent. Les deux bornes d'Abel sur tau(b)/b² et tau(b)(1+log b)/b² donnent bien les constantes affichées.

Le principal eulérien réel est `C_sf(rN)/r`, et le tilt a_N se convolue avec μ_N par le h_N de R10–R11. Pour le premier moment, la comparaison locale est avec **1/(p−1)³**, puis l'indice entier j=p−1≥2 ; une comparaison locale avec 1/p³ ne serait pas correcte. L'audit 3 explicite cette lecture et confirme les marges <2 et <4. Les préfixes acquis sont employés aux véritables arguments ≥N^(1/8), avec endpoints alpha et H payés par Abel.

R13/R14 conservent le vrai psi, ses puissances premières et le coût séparé des bases divisant N. Le niveau retenu q≤N^(7/16), le poids tau(q), le partage à u^L et l'input BV **all-prefix** permettent un gain logarithmique qualitatif indépendant. Ils n'utilisent pas une hypothèse de petites corrélations de parité. Les constantes classiques et le seuil supplémentaire de cette application BV restent **non évalués** ; l'onset acquis u≥10^24 de I ne les certifie pas automatiquement.

Avec R8, R9, R12, R14 et le retrait H u² de k=1, la conséquence écrite **P_head_all = O_A(N/u^A)** est justifiée sous ces inputs ; elle vaut aussi après retrait de la ligne k=1. C'est un résultat analytique partiel réel, sans preuve Lean nouvelle. Le banc fini n'énumère pas toute cette tête et n'en prouve pas les budgets asymptotiques.

La fermeture conserve exactement

`D_N=P_head^{>=2}+[P_tail^{>=2}−M^{>=2}]+I+2max(e,0)`.

Le bracket de **R16**, le bridge positif 2max(e,0) et la calibration commune des frais ne sont pas payés par le gain de tête. En particulier, la corrélation longue μ(r)Λ(N−3r)log r ne se réduit ni à BV seul ni à un préfixe multiplicatif acquis. La supposer petite dans un futur théorème déplacerait la cible.

## Témoins de support et de queue rejoués

| Témoin | Résultat exact | Raccord imposé |
|---|---|---|
| r=303, k=63, n=99980911 premier | Correct = 0 ; produit illégal d²t = −1 ; lcm ou restriction d = 0 | Conserver gcd(d,r)=1 dans R5, ou la formule générale à lcm |
| m=112211=11·101², n=99887789 premier | Tête entière 0 ; à B_cut=1 : −log101, queue +log101 ; tous deux actifs après Λ_N | Garder la queue ; aucun μ(m)² artificiel sur la coupe |
| m=173, n=99999827 premiers | Tout-k : −log173·log99999827 ; version k≥2 : zéro | Soustraire le point k=1 ou garder sa cancellation conjointe |
| b=21,c=101 | Fibre complète 0 ; fibre coupée non nulle | Garder le front cg≤H |
| b=3,c=41 | Somme complète −log3 ; somme coupée −log3−log41 | Garder le front cg>alpha |

Les domaines k tronqués conservent explicitement leur extérieur. La fibre r=99999727, K_r=1 est complète dans ce banc et son secteur k≥2 est vide ; cela ne rend pas complètes les autres fibres testées.

## Gram natif et poids réellement couplé

Les Gram premiers et CRT, leurs conjugaisons et axes zéro sont exacts dans les domaines testés. Le Gram droit conjugue la direction exceptionnelle ; la petite projection soustraite de son énergie n'est pas une petite énergie totale. Les facteurs locaux principaux induits gardent **rho_p**, pas une norme sqrt(p) fictive. La norme séparable exige deux vrais vecteurs séparés et conserve les +1 d'agrégation.

Sur **tout porteur physique DIV-HH m=rk** avec conducteur q|k et unités à N, la phase native vaut **χ(N−m)conjχ(N)=1**. Le témoin k=7 garde cette phase et la ligne centrée **5/6**, tandis que le twist bipolaire précédent est nul. Le noyau conserve ce secteur ; il n'y crée aucune oscillation supplémentaire. Le modèle C_HH−M_HH reste distinct de ses tuples physiques.

Le poids artificiel W=G quadratique falsifie seulement l'extension de la norme nue à tout poids couplé |W|≤1. Le vrai mineur **L2 h={3,13}, ell={101,311}**, arguments 303,933,1313,4043, a un déterminant du coefficient complet strictement positif. Tous les h sont premiers et h∤ell ; les logarithmes et dénominateurs positifs sont dégagés exactement. Le coin m=4043 a fII=0. Le n du point m=1313 est **23·59²·1249**, non carré-libre et correctement conservé au raw.

Ce mineur rejette une **séparation exacte de rang un** sur ces indices. Il ne réfute ni une séparation de rang supérieur, ni un Gram pondéré arithmétique futur, ni une estimation spécifique de HH. Le mineur avec h=1 reste un diagnostic raw hors L2. De même, les coûts N^(7/8) locaux et N^(13/8) du cumul absolu décrivent leurs majorations simplifiées, pas une minoration de la somme réelle ni une impossibilité globale.

## Décision de protocole

| Objet | Classification |
|---|---|
| R1–R7, cancellation conjointe et reindexage | EXACT_IDENTITIES_RETAINED |
| R8–R15 et gain de tête | ANALYTICAL_PARTIAL_HEAD_GAIN ; calibration supplémentaire non évaluée |
| R16 et cible complète | GLOBAL_SIGNED_BOUND_NOT_OBTAINED |
| Gram natifs nus | EXACT_ALGEBRA_RETAINED |
| Norme nue transférée sans paiement aux vrais poids couplés | MISSING_WEIGHTED_ARITHMETIC_ESTIMATE |
| Produits sans coprimalité, queues/caps/fibres supprimés, séparation exacte de rang un | SHORTCUTS_FALSIFIED_BEFORE_COMPILATION |
| Erreur Lean nouvelle | NONE_OBSERVED — aucun compiler invoqué |
| Condition de victoire | NOT_MET — aucun mécanisme complet certifié Lean |

Les raccourcis rejetés ne sont pas attribués aux identités corrigées présentes. Le progrès local de la tête est conservé, avec son domaine qualitatif. Le gain signé long et la compensation avec le modèle restent des obligations ouvertes ; aucun PASS fini ne les remplace.
