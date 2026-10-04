# Boucle 17 — annexe numérique C4 FINAL

Cette annexe nouvelle est distincte du FINAL6 initial et de ses 33 bindings gelés. Elle vérifie le moment et la queue des seize cœurs finis, sans relancer rough/TypeII, leurs replays, aucun W/kernel/Lean/PDF ni aucune estimation source. Les799 archives, le manifeste initial `c6e1efe0ef1e4c2448bb9d53eb6df1635b29eb9a077723620ce62d4f45a6b1e4`, ses33 bindings et les FINAL conceptuels sont vérifiés par hashes et demeurent intacts.

## Domaine et nouvelles identités exactes

Input unique : rough.json gelé SHA `e4dd2c8e12cbfd34c90208ffb90745472bc8e2c3a3f777681a9d52735fcadfbb`, seize cœurs non saturés avec rho/g/h effectifs et G_actual(100). N=10^8, P={2,3,5,7}, z=100. Ce choix fini ne prétend pas être le primorial au w=z^(1/32) du source C4. Tous les16 sous-ensembles par cœur sont enumerés exactement : poids W_s=produit h(p), produit naturel, logarithme formel et tête/queue. Fractions et encadrements de logarithmes sont rationnels, aucun flottant.

Les identités Z=Σ_s W_s=Π_p(1+h(p)) et, pour chaque p, coeff_logp(Σ_s W_s log(prod s))=Z*g(p) sont exactes. La queue prod(s)>100 est intégrale : produits105 et210, pour chaque cœur. G_P+Tail=Z et G_P≤G_actual(100) sont vérifiés par inclusion des quatorze produits de tête dans le support carré libre existant et égalité de chaque poids. Aucun noyau harmonique n’intervient dans ce calcul.

## Conditions mesurées et Markov sans division

M=Σ_p g(p)logp. La condition M≤log100/2 est TRUE_FINITE pour 7, 21, 31, 43, 57, 73, et FALSE_FINITE pour 13, 19, 33, 37, 39, 51, 61, 67, 69, 79. Les dix `CONDITION_FALSE_FINITE` restent des résultats ; la condition n’a jamais été imposée pour obtenir un PASS.

Pour les six premières lignes : Z=105/8, G_P=99/8, Tail=3/4. Pour les dix autres : Z=35/2, G_P=97/6, Tail=4/3. Les seize marges de Markov `(G_P−Z)log100+Z*M` sont strictement POSITIVE, et chaque queue a log(prod s)−log100 strictement positif. La borne générale G_P≥Z*(1−M/log100) est ainsi gardée dans sa forme sans division. La conclusion observée G_P≥Z/2 vaut ici même lorsque la condition suffisante de demi-moment est fausse : cette condition fausse ne réfute donc pas la conclusion observée, et ne permet pas de la déduire gratuitement dans un autre domaine.

L’annexe a64 nouvelles positions de certificats :32 queues,16 conditions et16 Markov. Elles sont comptées séparément des390 positions initiales ; ce ne sont pas64 théorèmes. C4/C6/U4/BV source ne sont pas appliqués au N fini, et le seuil source u≥10^24 ne reçoit aucun verdict à partir de ce tableau.

## Exécutions, gel et hashes

Un essai canonique réel exit0, snapshot pré-exécution et log conservés ; aucun échec réel ou fabriqué. Un seul replay isolé réel exit0, identique en octets et en champs. La clôture lit seulement les preuves stockées, contrôle leurs bornes et hashes, sans producer/sign/kernel rerun. Source et gate PASS sont immuables.

Source `role6_c4/moment_checks.py` SHA `613a38487ff8016c30e4f93fcdd5c3dd3a4fe54b10924f66ee200e246274617b` ; snapshot identique. Gate `role6_c4/moment.json` et copie `role6_c4/isolated/moment.json` SHA `d78c0cdc941cc2950e43168ed53809108aa55bffe0db31672905c2e5d2f7a5a6`. Log canonique `a4081706fb0475fa49c1ef9c9cd29939f2f9dd608e45164f4831a0e03b24a459` ; reçu de copie `feaedbbe7cf0e3a1aeb987331565f8ae79f91fd323604436dcdba1005b09a367`. Helpers, scripts de capture, logs, outputs et reçu final distinct sont liés dans `role6_c4/manifest.json`.

Portée : nouvelle annexe moment/queue/Markov seulement, aucune nouvelle disponibilité, capacité globale, estimation de Gamma ou whole D_N. Ledger entier et erreurs hors support demeurent non payés. Zéro Lean par ce rôle, aucun recompte des dépendances historiques, score0/victoryfalse. Le FINAL6 initial n’est ni corrigé ni rouvert ; la recherche globale continue.
