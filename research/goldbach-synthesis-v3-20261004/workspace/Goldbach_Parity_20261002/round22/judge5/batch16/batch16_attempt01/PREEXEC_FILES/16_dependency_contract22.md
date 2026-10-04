# Log32 → coefficients entiers : contrat SOURCE52 révision02

Statut : SOURCE_ONLY_NOT_COMPILED. Ce paquet contient deux nouvelles sources, 52 déclarations explicites (20 définitions et 32 théorèmes) et 52 commandes #print axioms qualifiées. Aucune invocation Lean, aucun import ou calcul Python, aucune préparation de lancement et aucune banque numérique n'ont eu lieu pour ce paquet. Il ne revendique ni PASS ni victoire.

Les paramètres repris du handoff immuable ROLE4 sont N=M=100000000, K=2^27 et S=2^58. Le paramètre a=0 concerne seulement le polynôme fini ; aucune trace infinie T_0 n'est définie ici. Les deux modules ne dépendent d'aucun nouveau module de projection SOURCE ou objet non validé ; ils utilisent directement mathlib et leur dépendance locale explicite.

## Constructeur et vraie précision

RationalLogQuantization22 définit k=Nat.log2 p, z=(p−2^k)/(p+2^k) dans Q et L32(z)=2 Σ(j<32) z^(2j+1)/(2j+1). Le point de départ analytique est le vrai HasSum de log(1+z)−log(1−z), disponible dans le cache mathlib4.15. Pour 0≤z≤1/3, chaque terme après32 est majoré par (2/65)*3^−65*(1/9)^j. Le vrai HasSum de la queue et celui de la série géométrique donnent l'enveloppe R32=9/(4*65*3^65), avec ses deux signes.

Pour 2≤p≤N, les propriétés Nat.log2/Nat.log prouvent k≤26 et 2^k≤p<2^(k+1), puis 0≤z≤1/3. L'identité logarithmique log p=k log2+log(1+z)−log(1−z) est prouvée par les vraies opérations log/div/pow, avec tous les dénominateurs non nuls explicités. Les bornes de log2 sont elles aussi produites par L32(1/3), et non fournies en entrée.

Les fonctions rationnelles logLowerQ, logWidthQ et logMidpointQ sont les mêmes expressions que dans le modèle final ROLE4. log32_enclosure est une conséquence de la chaîne précédente. log32_width_small paie une borne suffisante width≤1/S par k≤26 et les constantes exactes ; la borne documentaire plus forte width<2^−96 n'est pas postulée et n'est pas nécessaire à ce théorème.

nearestEven agit sur le rationnel S*midpoint, utilise Int.floor et la partie fractionnaire, puis choisit l'entier pair exactement en cas de demi. Il ne remplace pas ce point par floor(S*Real.log p) et ne suppose pas un comportement de Real.round. La borne d'arrondi ≤1/2 vient des deux vraies propriétés du plancher. clampInteger borne le point dans [0,32S] ; sa propriété de contraction est prouvée par les trois positions possibles par rapport à cet intervalle. Enfin, true_log_bounds prouve 0≤log p≤32 directement par log p≤log(2^32)=32 log2≤32. Ces étapes donnent quantizedLog_precision : |log p−logPoint(p)/S|≤1/S, sous les seules gardes 2≤p≤N.

## Vrais poids et coefficient

QuantizedLambdaEnvelope22 définit integerLambda(n)=logPoint(minFac n) si IsPrimePow n, zéro sinon ; quantizedLambda=integerLambda/S. Le vrai vonMangoldt utilise exactement cette même branche IsPrimePow et log(minFac n). La précision et la borne 0≤Λ(n)≤32 proviennent directement de minFac_prime, minFac_le et des théorèmes du premier module. Le lemme vonMangoldt_le_log n'est pas utilisé. Chaque puissance de premier propre reste présente.

Le coefficient vrai est Σ(n≤N) Λ(n)Λ(N−n), et le coefficient entier canonique est Σ(n≤N) integerLambda(n)*integerLambda(N−n). L'égalité entre ce coefficient entier divisé par S² et les produits quantifiés est prouvée par les sommes finies et les morphismes de cast. L'erreur d'un produit est majorée par64/S, en utilisant les deux bornes32 effectivement établies et les précisions issues du constructeur. La somme donne même la borne (N+1)*64/S, donc également l'enveloppe demandée

E(N,S)=(N+1)*(64/S+1/S²).

coefficient_error_bound ne prend ni précision, ni majorant de Λ, ni coefficient cible en prémisse. errorEnvelope_continuousOn paie la continuité réelle sur S>0. fixed_integer_tau_guard écrit la garde entière exacte 2*(N+1)*(64S+1)*10^6≤S². Les constantes de cette garde restent une obligation de vérification Lean, car ce code SOURCE n'a pas été compilé.

## Dépendances et dettes séparées

Les sources et preuves mathlib ont été consultées en lecture ciblée ; ces consultations ne constituent pas une compilation. Les reçus distinguent les sources FULL, les APIs TARGETED et les chemins importés seulement identifiés/hachés. Aucun ancien PASS numérique n'est utilisé comme oracle.

La réalisation native doit encore vérifier l'égalité de chaque enregistrement entier avec le constructeur canonique A32. Les queues/endpoints natifs communs, les divmod exacts, les retenues et les casts de mots sont des obligations distinctes. ROOT a retenu explicitement la garde indépendante d'égalité au constructeur, en plus des bornes. Ce paquet ne suppose aucune de ces égalités d'enregistrements.

Les catalogues natifs doivent aussi certifier la classification prime/pouvoir et le minFac de chaque entrée, puis la NTT exacte, le sens de ses racines, les alias, la reconstruction CRT et l'absence de débordement. Ces charges ne sont pas masquées par coefficient_error_bound. Aucune précision flottante libre, aucun coût mesuré, aucun nouveau résultat NTT n'est affirmé.

L'identité géométrique du cercle et sa compilation indépendante sont des travaux séparés. Même après validation de ce paquet et d'une future évaluation finie à N=10^8, le transfert global H1, la condition analytique de phase, le contrôle D_N et la WIN de la directive restent ouverts. Une somme exacte ou quantifiée d'un coefficient fini reste une boussole arithmétique certifiable, sans implication automatique de contournement du mur de la parité.
## Révision SOURCE distincte et conservation

Les premières sources d7ea4d46f0c595c05ccb140ee310996e3c257a240bde29a58c6a7c7811bce396 et428836508d2edfe22c4639101f0b7a99ff34dbf57ea9375b72ab509e410ec1a3 restent intactes. ROLE4 les a relues FULL (1dfa9c/c3a330), en SOURCE/papier seulement, et confirme la correspondance rationnelle nearestEven/divmod et les branches PP/minFac. Aucun FAIL Lean n'a été observé sur ce paquet.

La révision02 conserve exactement les 52 en-têtes et domaines. Quatre passages de monotonie sont désormais explicites : width≤27R utilise mul_le_mul_of_nonneg_right ; la borne |logp−mid| est multipliée par S via mul_le_mul_of_nonneg_left avant nlinarith ; la borne logp≤32 est également multipliée par S avant le clamp ; le terme positif1/S² de l'enveloppe utilise mul_le_mul_of_nonneg_left. Cela évite de faire dépendre les arguments de la génération automatique de produits par une tactique. Toutes les définitions du constructeur et les #print sont inchangés.

Le paquet proposé est maintenant la paire de modules dans revision02. Les premières sources ne doivent pas être mélangées avec les copies de cette révision lors d'une future préparation. Aucune compilation, aucune préparation de runtime et aucun test numérique n'est autorisé par ce handoff SOURCE.