# Agent 6 — reçu final, boucle 8

2 octobre 2026. **N = 100 000 000** reste fixé. Les trois PASS ci-dessous concernent des identités finies et des falsificateurs exacts. Ils ne valident ni le paiement analytique de I, ni un gain du moment HH, ni une borne globale sur D_N. Aucun script n'appelle Lean ni ne modifie le nombre de certificats.

## Compensation signée et vrais supports

`compensation_checks.py` / `compensation.json` vérifient `S_full(E)=S_Lambda(E)-I(E)` et la réindexation par P_k(E), M_k(E), en gardant le même indicateur de sélection E sur chaque côté. Domaines : m=1..303, m=1..1024, puis les cinq arguments isolés 841,909,10201,30603,658911. Les faces αk<m, m≤N−2, k≤Q, gcd(m,N)=1 et gcd(N−m,k)=1 sont calculées exactement. P1=M1 ; les entrées k=1 de D et W sont toutes deux −log(m) et s'annulent point par point.

La bascule `μ(k)μ(kr)=μ(k)²μ(r)1_(gcd(k,r)=1)` est testée sur **65536 couples**, k=1..128,r=1..512, plus des exemples avec puissances premières et facteurs répétés. L'expansion carrée-libre du rang k est vérifiée sur sept domaines explicitement déclarés, totalisant **1408 emplacements k**. Les troncatures k<K_r conservent leur extérieur non calculé ; r=99999727,K_r=1 est complet et sa ligne k≥2 est vide. Les conditions gcd(d,rN)=1 et t|rad(r) restent visibles.

Les puissances premières unitaires du premier axe restent dans Λ_N et le raw ; par exemple n=9967²,m=658911. Les puissances 2²⁶ et 5¹¹ sont exclues exactement par les unités N. Aucun μ(n)² n'est ajouté au raw. Les coefficients logarithmiques sont rationnels ; les signes éventuels utilisent les intervalles rationnels artanh de round3, sans oracle flottant.

## Tête physique et coupe par la partie carrée

`head_regrouping_checks.py` / `head_regrouping.json` vérifient le regroupement par `q=b²c` et `w(q)=μ(b)μ(c)sum_(g|b,α<cg≤H)μ(g)log(cg)` sur **12 m sélectionnés**, pas sur toute la tête. Les supports b,c carrés-libres, gcd(b,c)=1, gcd(bc,N)=1 restent exacts. H=1000 est floor(N^(3/8)); B physique=1 est floor(N^(1/32)), établis par puissances entières. Les autres B=2,4,8,16,128 sont des coupes de stress algébriques finies, pas des choix asymptotiques alternatifs.

Trois raccords sont certifiés :

* r=303,k=63=3²*7,n=99980911 premier. Autoriser d partageant r tout en gardant d²t produit le coefficient erroné −1 au lieu de zéro. L'exclusion gcd(d,r)=1 ou le lcm général rétablit le bon détecteur.
* m=112211=11*101²,n=99887789 premier. La tête complète vaut zéro ; la coupe B=1 garde **−log101 log99887789**, compensée par sa queue **+log101 log99887789**. Ajouter un filtre carré-libre à la tête tronquée serait faux.
* m=173,n=99999827 premiers. La tête avec k=1 contient **−log173 log99999827**. Il faut le soustraire pour k≥2, ou conserver son annulation conjointe avec HARM.

Les fibres complètes utilisent la somme divisorielle log(c) si b=1, −Λ(b) si b>1. Les fibres incomplètes restent littérales : b=21,c=101 et b=3,c=41 réfutent leur remplacement par la formule complète. Le compte sans +1 vaut uniquement pour le préfixe spécial n=N−qv,1≤v≤floor((N−2)/q) ; les +1 d'autres intervalles/fibres ne sont pas supprimés. Aucun préfixe ψ_N complet ni complément r>H n'est énuméré.

## Matrice native, conjugaisons et couplage

`native_gram_checks.py` / `native_gram.json` contrôlent **9339 entrées de Gram** pour tous les caractères non principaux aux premiers q=3,7,11,13,19, sur tous les résidus a,b, zéro compris. Les phases sont des polynômes entiers réduits cyclotomiquement. Elles vérifient `GG*=qId−χ(a)conjχ(c)`, le Gram unitaire `qId−11*−vv*`, et l'énergie `||Gβ||²=q||β||²−|sum χ(b)β_b|²` avec β complexe explicite. L'ordre 4 modulo 13 falsifie les conjugaisons inversées. La norme pleine sqrt(q) est exacte : Gram pour la majoration et colonne zéro constante pour l'égalité.

Les **6120 entrées CRT** aux modules 21 et 33 incluent les caractères localement principaux. Les matrices principales réelles ont la caractéristique entière attendue : les deux racines de x²−(p−1)x−1, et les autres valeurs ±1. Cela certifie rho_p=((p−1)+sqrt((p−1)²+4))/2 sans comparaison flottante. Sur unités, leur norme vaut p−2. Le secteur q|k est conservé : k=7 donne C=0 modulo7, G(C,ζ)=1 et rang natif 5/6 ; le nouveau twist bipolaire nul ne le remplace pas.

Le transfert de la norme à tout poids couplé |W|≤1 est falsifié exactement par W=G quadratique : la somme vaut q²−q+1 et son carré dépasse q³. Ce poids artificiel ne réfute pas une estimation du poids HH particulier.

Le mineur générique raw h={1,3},ell={101,311} est positif ; **h=1 est hors L2**, cette portée est explicite. Un vrai mineur L2 h={3,13},ell={101,311} est aussi positif pour le coefficient complet `μ(ell)log(h)/log(h*ell)F_N(h*ell)`. Le coin m=4043 est nul ; le signe est donc certifié après dégagement des dénominateurs positifs. m=1313 a n=23*59²*1249 non carré-libre et demeure au raw. Ces mineurs réfutent seulement la séparation exacte de rang1 sur ces indices, pas des décompositions plus riches ni un Gram pondéré futur. Aucun coefficient réel n'a été remplacé par une matrice séparable dans le banc.

## Onset, conservation et rejouabilité

Le reçu visuel `source_onset_render_receipt.json`, fourni par le contrôleur avec le hash du PDF original et ses pages32/33/36, fixe l'onset adaptatif **u≥10²⁴** : l'extraction avait perdu l'exposant. N=10⁸ est sous cet onset et ne valide que les identités finies. Le domaine analytique acquis de I reste celui de la monographie. Les préfixes légitimes X=1024 ne sont pas modifiés.

L'inventaire initial donne exactement **227 anciens artefacts**, tous conservés. Son helper pointe explicitement sur `round8/previous_artifacts_sha256.json`; round8 entier, caches, .arbor et REPORT.md vivant sont exclus. Les fichiers de round7 et avant n'ont pas été touchés.

Les trois scripts acceptent `--output-dir <dossier>` pour le Juge : seules les nouvelles sorties JSON y sont écrites, le registre de conservation reste lié à round8. Le replay isolé de native_gram.json produit le même SHA-256 que le reçu canonique. Durées locales environ 0,3–1,1 s par banc ; elles correspondent aux domaines déclarés, jamais à un calcul global.

| Fichier round8 | SHA-256 |
|---|---|
| compensation_checks.py | b6dc5fbb7e35b5bad93c54513970845c5bf721573a7e2513742d20ebc4a62262 |
| compensation.json | 44fb25267eb3088037ef6d16bb3998a42a94952576662f279c35527aa702364c |
| head_regrouping_checks.py | 4e2b87f912177f05871bdefd6d532db99ca02ec1ac888cda5bfb9032ad3eb65e |
| head_regrouping.json | f85071f0d1f6f1ecfd1d9612caf8d874bd9669933fd47fc00ae9ffffbc3cd7eb |
| native_gram_checks.py | 27ef19aa273a40569ffba4fa00cd6f9aec5d9a911e126f1efc450656e7b3d5a6 |
| native_gram.json | ac4a14ae8a58a1579c16d84dd70aeac97e610b62b61514ff176e8bd0b8676ed0 |
| shared.py | d7d38a641a49827c0be3f0b1dc1d07b8c18b514b7d2721515191b44720b934cb |
| conservation.py | 9c515fed1caa327154879d6754cd962948dae8f0be89ded3e3cbee018a7b62b8 |
| previous_artifacts_sha256.json | b973b6ea8ce1fdef2a704e1e0bcc977ee7ac5b140e71d17cc3d90c165317243a |

Les domaines omis et les queues restent non calculés. Aucun PASS analytique ou victoire sémantique n'est attribué.
