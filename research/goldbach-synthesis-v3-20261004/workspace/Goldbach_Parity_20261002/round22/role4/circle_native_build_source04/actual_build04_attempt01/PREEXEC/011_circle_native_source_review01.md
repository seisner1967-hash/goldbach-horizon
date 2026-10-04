# Revue indépendante native SOURCE01 — circuits écrits, exécution ouverte

ROLE5, distinct de l'auteur ROLE4. Statut : SOURCE_REVIEW_COMPLETE_RUNTIME_OPEN. Lecture et contrôle des bytes uniquement ; zéro build, parser natif, import de modèle, probe, run ou nouvelle banque. Aucun PASS natif, chiffre de coefficient à 10^8, H1, D_N ou WIN. Baseline officielle 76 modules/1252 déclarations ; FAIL16 technique séparé ne paie pas la paire Log52.

## Sources exactes et portée de lecture

Dossier auteur immuable : `D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/circle_native_source01`.

| Fichier | SHA256 | Lecture indépendante |
|---|---|---|
| producer_dit22.cpp | bdb7b022ae20ed8dce02959b77db62ca690a9798393292db62edf262d938ed74 | FULL f3ae6b |
| checker_dif22.cpp | 239c45b41f1a60a690664c0d01387c00c74f8e4b8c7ded59b716866fef098648 | FULL 858516 |
| native_contract22.md | 4f01d07973c22ad1e75019068dc65fdc0e01fe1812629239d8af2557dc983870 | FULL 93b151 |
| source_handoff22.json | 7c5eb71cc23ac7f4235bd566e8aa5e07653a756fab6c58ad4a61aa183e11f834 | FULL 0ff238 |
| inventory22.json | 5876da3e3bf901035adca1e0c7dc4b3981ef457f2fe5d92000662e44203ed2d0 | FULL 150637 |
| read_receipts22.json | 9b0cdc14e47dbe428067bfeda50bffafe44b6d57b87d39bd280ea9f595987f5d | FULL f000a6 |

Métadonnées 7f8231 : 55 bindings uniques, tous SHA et tailles vérifiés, zéro changement. Cela ne constitue aucune lecture FULL des headers/binaries inclus. GMP header178db669… : signatures import/export/divexact/fdiv_qr/fdiv_ui/invert/pow_ui/gcd/get_str/set_str/sizeinbase et macro odd_p TARGETED 9eeaab seulement. Mathlib/NumberTheory/LucasPrimality.lean bdf50c28… relu FULL98659c ; vraie signature lucas_primality et existence du témoin. Les anciens PAPER19/revues et olean Identity13 sont readonly, aucun replay. Références de lignes natives contrôlées par rg635aae.

## Catalogue et vraie Λ

Le producteur parcourt toutes les premières divisions d'essai ; il ne construit aucun crible combinatoire. Le checker revalide chaque entry n : un facteur p<n est divisible, premier certifié à un indice antérieur ; p=n impose un record trié et Lucas avec factorisation complète de n−1. distinct_factors exige r<n et q<n ; des entries futures chargées en mémoire ne servent pas de certificats non vérifiés. Chaque division enlève toutes les valuations, donc les facteurs distincts couvrent n−1. Les tests a^(n−1)=1 et a^((n−1)/q)≠1 pour tous ses facteurs premiers correspondent au vrai lemme Lucas. Le cas n=2/g=1 a une liste de facteurs vide valide. Les tailles exactes et count contrôlent l'absence de trous/records supplémentaires.

Le checker accepte un facteur premier quelconque. Cela suffit pour Λ : si l'extraction de sa valuation laisse1, n est une puissance de cette unique base première, donc cette base est minFac ; sinon n n'est pas une puissance première et reçoit0. Tous PP sont conservés. Le pont formel entre cette induction native et IsPrimePow/minFac n'est toutefois pas écrit dans un module compilé ; aucune primalité du catalogue entier n'est acquise par cette lecture.

## Constructeur canonique et erreur

series32 multiplie le produit H des impairs par d^63. Son numérateur de terme 2a^(2j+1)d^(62−2j)H/(2j+1) représente exactement le terme rationnel 2 z^(2j+1)/(2j+1) au dénominateur commun. Le checker reconstruit indépendamment la somme par fractions réduites. Les deux réductions donnent le même entier k=floor(log2 p) et z=(p−2^k)/(p+2^k), dans[0,1/3] pour2≤p≤10^8. Les bornes lo/hi comportent réellement le reste (k+1)9/[4(2m+1)3^(2m+1)] ; il n'y a pas d'epsilon libre.

Les circuits effectuent floor du midpoint rationnel mis à l'échelle, comparent exactement2r au dénominateur, choisissent l'entier pair en cas d'égalité et appliquent le même clamp[0,32S]. Le checker exige, ligne192, equality du record au constructeur canonique32. Cette exigence ferme sur SOURCE la dette d'encloser40 seul relevée dans la revue PAPER929979f… ; la fraction réduite ne change ni midpoint ni tie. L'encloser40 des deux endpoints du record est une vérification supplémentaire distincte. Après libération du buffer NTT, le checker reconstruit ses nouveaux points40 pour B ; il ne recycle pas les pointsA32 comme référenceB.

Sous les vrais lemmes de logarithme/arrondi et la réalisation des mots, les bornes |Λ−A/S|≤1/S et0≤Λ,A/S≤32 donnent64/S par produit, donc E=(N+1)(64/S+1/S²) par coefficient. La comparaison entière |cA−cB|≤2(N+1)(64S+1) est exactement2E après division par S² ; la garde tau multiplie réellement par10^6. Continuité de E sur S>0 ne généralise pas le constructeur au-delà du S=2^58 fixé. Aucune égalité/distance finale n'est supposée en entrée. Les pointsB peuvent coïncider avecA : ce contrôle de proximité seul n'est pas un mutant discriminant ni une preuve d'indépendance de GMP. La paire Lean52 n'a pour l'instant aucun PASS indépendant après FAIL16 ; le modèle SOURCE et ces circuits ne remplacent pas ce crédit.

## Transformées, CRT et mots

Les cinq paramètres sont exactement ceux du PAPER, p=cK+1 avecK=2^27 ; le producteur contrôle toutes divisions jusqu'à√p, le checker toutes divisions impaires après p impair. Les deux vérifient ω^K=1, ω^(K/2)≠1 et les inverses par produit1. Aucun de ces tests n'a été exécuté ici. DIT utilise entrée bit-reversed puis racine positive ; DIF utilise entrée naturelle, sortie bit-reversed puis reverse27. La réduction emploie ω^(−Nj), somme divisée parK. Pour M=N<K, les fréquences m+n−N appartiennent à[−N,N], donc le seul multiple deK est0 malgré2N>K. Le signe et la normalisation ciblent bien le coefficientN.

Le CRT incrémental et le CRT par bases sont deux circuits distincts. Produit des moduli>2^154 et coefficient<(N+1)2^126<2^153 permettent l'unicité ; le checker impose en outre equality au foldA direct et aux cinq résidus. Les résidus uint32 sont canoniques ; products promus uint64 sont<2^64, additions/soustractions<2^33. Les boucles/index/shifts NTT restent dans les plages uint32 pour les constantes fixées.

La décomposition32/64 du produit de deux points≤2^63 ne dépasse pas uint64 dans t/u/high. low=(u<<32)|(base&mask) exploite la réduction unsigned modulo2^64 avec champs disjoints. L'accumulation192 transmet le carry du low au middle puis au high ; c1+c2≤1 et high<2^25 sont gardés. Cette analyse SOURCE n'est pas le lemme de raffinement des trois membres vers l'entier mathématique. GMP reste une primitive partagée non certifiée. Les caps4096/8192 et CRT192/256 portent sur les résultats, pas sur toute allocation temporaire interne. Aucun déficit arithmétique concret n'a été trouvé dans ces identités à la lecture ; preuves formelles NTT/permutations/CRT/carries/catalogue et sérialisation demeurent ouvertes.

## Déficit de ressources précis et portée du livrable

Premier défaut SOURCE local repéré : checker lignes132–133 incrémente d de2 depuis3, donc d est toujours impair et `!(d&4095)` est toujours faux. Le tick prévu dans cette boucle de divisions n'est jamais appelé. Corriger dans une révision distincte par un compteur d'itérations ou une condition adaptée aux impairs. Cela ne réfute pas le test de primalité ; aucune invocation n'a constaté de dépassement. Plus généralement, les3600s sont un délai coopératif par exécutable, donc ne constituent ni un hard wall ni une limite globale producteur+checker.

Les constants payload1736870924 et réserve134217728 donnent1871088652 bytes de proposition, pas une mesure RSS ni une borne garantie de GMP/OS. Catalogue/records headers<=1200000060 bytes et claim<=4096 sont explicitement bornés ; les charges logs/disque/processus et clôture transitive includes/link/ABI restent ouvertes. Coût SOURCE :40265318400 produits modulaires principaux +10 normalisations/setup,288P termes de série en incluant log2 recalculé, deux folds N+1, divisions complètes et recherche Lucas. Pas de temps mesuré ni de promesse de terminaison à3600s.

Le contrat est finiment calculable avec deux .cpp concrets ; le programme n'est ni construit ni runtime PREPARED et aucun banc coefficientN n'est terminé. Les identités continue/discrète auxiliaires déjà Lean PASS restent acquises, mais ne certifient pas ces implémentations natives. Un petit PARAMETER_GUARD distinct ne paierait pas l'exécution complète du catalogue/NTT. Corriger le tick, payer build closure, protocole immuable, hard wall/RSS et preuves de raffinement nécessite de nouvelles sélections explicites ROOT ; cette revue ne prépare ni n'autorise leur exécution. H1 spectral uniforme, PP/frontière, D_N et WIN restent ouverts.
