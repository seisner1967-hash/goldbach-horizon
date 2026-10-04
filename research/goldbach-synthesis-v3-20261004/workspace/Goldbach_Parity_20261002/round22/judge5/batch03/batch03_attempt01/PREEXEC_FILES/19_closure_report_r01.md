# Clôture du banc componentiel R01 — portée auxiliaire

Le seul essai autorisé de la révision01 a produit
`THERMAL_COMPONENT_R01_AUX_PASS`, exit0. START réel :
2026-10-03T10:41:16.513468UTC ; FINISH réel :
2026-10-03T10:44:48.631579UTC, soit212.118111secondes.
Token : `b18e551101074db984ae7a7f0875d94f`. Launcher028eed/session69218,
achèvement6e379e. Aucun retry, ancien producteur ou ancienne valeur partielle.

Le résultat porte46cas. Les deux régressions de transport des rayons,
exposants512et768, s'accordent avec une nouvelle exponentiation entière
gaussienne indépendante. Les15casΓ de σ∈{1,3/2,2} et
γ∈{0,−5,5,−19,19} s'accordent en phase complexe avec une nouvelle quadrature
de l'intégrale définissantΓ et avec les références de norme. Chaque référence
utilise2240cellules,33600au total ; toutes les15comparaisons de phase sont
signalées informatives. Les4casΓ aux extrémitésσ5/16,43/16 etγ±100
contrôlent uniquement domaine et largeur : aucune référence indépendante de
phase n'est attribuée à ces4cas.

Les2casEM comparentζ(0),ζ(2) aux constantes exactes ;ζ′(0) a sa référence
indépendante. Les8casEM restants, Re s∈{−11/16,−5/16,21/16,27/16},
Im s=±1597/16, sont des contrôles de domaine, de dénominateur et de largeur,
sans référence indépendante de leur valeur. Les8polynômes verticaux de
degrés0,1,2,3,4,16,32,64 et5polynômes réels de degrés0,1,2,31,32
s'accordent avec leur intégrale exacte. Les2contre-tests d'alias de degrés128
et96 retrouvent l'alias payé et un écart non nul avec l'intégrale véritable.
Les quatre budgets fonction/position/poids/accumulation restent distincts.

Les19mutations sont déclarées disjointes de leur référence :15multiplications
deΓ par i,2changements de signe deζ,1changement de signe deζ′(0),
1omission des i^k dans l'intégration verticale. Le checker indépendant exécuté
dans l'unique enfant termine avec `checker_PASS=true`, sans erreur. Il ne
réimporte pas le producteur. `failures=[]` et `unresolved=[]`.

Le transport enregistre50720arrondis de rayon, un supplément outward total
majoré par24431/2^511, et au plus513bits de dénominateur pour les rayons.
Les50944produits de points correspondent au catalogue fixé. L'export JSON
termine avec la limite entière Python inchangée. Le défaut technique de l'essai
original reste archivé ; aucune comparaison partielle de cet essai n'a été
utilisée comme oracle.

Lecture ROLE6 : receipt/START/log complets6e379e/e02c33 ; résultat235516octets,
3395lignes, JSON entièrement parsé. Toutes les46entrées de catalogue et leurs
décisions, les19mutations et les limites de portée ont été projetées et lues
sans troncature744b84. Compteurs et checker lus e02c33/c22c78. La sortie
c22c78 comportant les grands rationnels des mutations était tronquée ; elle
ne justifie aucune prétention de lecture brute complète des3395lignes.
Il n'y a pas eu de réexécution du checker ni de recalcul des intervalles après
l'enfant autorisé. La clôture vérifie seulement métadonnées, SHA et captures.

RésultatSHA :
`c43622616022e65991aee5a12d189d3bae142db1f2d347cb131e8abd685c7a6c`.
ReceiptSHA :
`675fd4efcb6fc038b142c89eb6ff7843d57072a596e144cb52e8c681bdb76500`.
LogSHA :
`97d4abaca2a3767297a524b8aba1c00f7b064d0c1b1324ba831c53f2463c4dd4`.
CertificatesSHA :
`553cd8b9debcbacce4b68696e636d5a692bdcde0a39630f4b524eeb98f7e6e77`.

Ce PASS appartient uniquement à `THERMAL_COMPONENT_R01_AUX_ONLY`.
H1 numérique et formelle, coefficientN, D_N etWIN sont tousfalse dans le
résultat. Les15certificats de racine et les35captures PREEXEC sont conservés.
Les33bindings R01 et les25bindings originaux font l'objet d'une vérification
SHA après exécution. Le banc est désormais fermé et ne sera pas rejoué.

Deux brouillons futurs, `global_h1_source22/unit_transport_source22.py` et
`global_h1_source22/arithmetic_source22.py`, ont été écrits en source seulement,
hors du gel R01. Ils n'ont été ni importés ni exécutés. Leur statut demeure
DRAFT_SOURCE_ONLY, sans gate, banque globale, coût mesuré ou crédit H1.

