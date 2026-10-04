# Préparation du Juge19 — aucun lancement autorisé

Les fichiers `audit.py`, `run_once.py` et `authorization_schema.json` sont
des sources préparées. Ils n'ont pas été exécutés, compilés ou sondés.
Le fichier définitif `preparation.json` n'existe pas à ce stade : FINAL3/4 et
les deux FINAL6 sont désormais gelés et relus, avec les onze sources finales.
La dernière observation root FINAL3 est désormais écrite et lue intégralement.
Toutes les lectures gelées nécessaires à l'inventaire metadata sont faites.
La racine a lu intégralement audit.py au SHA256
8aabf796e9ec5cf135ab5c1bf76f9f3eb791e02b9f681153c7216e30df967117
et run_once.py au SHA256
f7e22678da62c0fb1613c463bf5cb9f539e2cec88cf2db869b63c533486e36bd.
Aucun delta de ces deux sources n'a suivi ces lectures, et aucun gate du
Juge n'a encore été émis.

La sous-revue papier role1_gap_review est également FINAL gelée et relue avec
son reçu. Elle est incluse dans les gels requis avant l'inventaire de round19,
pour éviter de lier des empreintes concurrentes. L'observation root FINAL3
est également incluse dans les inputs du futur gel metadata.

La préparation définitive devra contenir :

- les hashes exacts de tous les inputs FINAL19 nécessaires, avec chemins
  relatifs à Goldbach_Parity_20261002 ; les sources, logs et captures de
  toutes les tentatives auteurs, y compris les échecs techniques et les
  événements de lancement avant Lean, seront inclus ;
- la liste topologique des onze modules neufs seulement, leurs namespaces
  et les deux prints générés FactorTuple.ext et SignedCoordinates.ext ;
- les deux banques nouvelles, leurs résultats, vrais reçus canoniques
  exit0, FINAL6, signatures et champs effectifs de contrat ; aucune banque
  ou kernel historique ne sera exécuté ;
- les sources et oleans Judge18/build, Judge16/build et13/dependencies
  requis en lecture seule, huit bibliothèques cache mathlib, HEAD vérifié,
  Python/Lean SHA et métadonnées de version déjà acquises, sans sonde Lean ;
- les hashes des originaux PDF/ZIP et du registry1361, les rapports FINAL
  et les observations du coordinateur qui attestent les gates réellement
  franchis ;
- la liste explicite des obligations sémantiques ouvertes : positivité du
  coefficient IE/M réel, K14, raccord AP ordinaire et exceptions/endpoints,
  cumul de multiplicité des trois familles, K18/onset BV, Gamma_rank,
  canal long/medium, nouvelle couche rho/Selberg/H9, segment10^24..10^40,
  rangs>=4, T_A, comparaisons parents, capacités et ledger entier.

Le lanceur refuse l'exécution sans une autorisation distincte de la racine
`ROOT19_JUDGE_CANONICAL_ATTEMPT01`, après sa lecture intégrale des deux
sources et de la préparation définitive. Il conserve ensuite ses sources,
l'autorisation, la préparation et les onze sources exactes PREEXEC, puis
la commande/cwd/runtime et le reçu de l'unique subprocess d'audit.

L'audit vérifie les fichiers et données stockées. Les contrôles entiers de
nonSS multiplient les multisets déjà fournis et contrôlent les coordonnées
et inverses enregistrés ; ils ne refactorisent ni ne testent de primalité.
Les contrôles rationnels H8 et l'encodage des intervalles/sign labels restent
distincts d'une nouvelle évaluation de log, W/D, prix ou signe. Les positions
de certificats comprennent les champs répétés du JSON et ne comptent pas
des expériences indépendantes.

Le stage de rang est indépendant du producteur. Il décompresse le bitmap
existant sans refaire un crible, compare chaque progression entière aux
member rows stockées et vérifie les masques d'unités/face. Les vrais témoins
beta sont contrôlés par leurs produits, ordres et fronts sans retester de
primalité. Les diviseurs IE viennent des facteurs déjà fournis, avec tous
les exposants et les mu=0. Les références et les coefficients exacts sont
reconstruits comme rationnels et raccordés à leurs digests ; K4 et le split
raw/theta/PP sont vérifiés sur ces coefficients sans évaluer les logs. Les
APmember indices et les trois développements T0/Ts/TFs sont conservés pour
les deux R, avec chaque représentation de module et la multiplicité cumulée.
Les boîtes affines gardent honnêtement PARAMETER_BOX_MAY_CHANGE_SIGN lorsque
les endpoints stockés ne donnent pas de signe commun.

Le build du Juge est neuf et n'utilise aucun olean auteur19. Chaque Lean
conserve son propre PREEXEC, stdout et stderr binaires séparés, log combiné,
exit et reçu d'invocation avant toute assertion de validation. Les axiomes
de toutes les déclarations et des extensions imprimées doivent être parmi
propext, Classical.choice et Quot.sound. Les warnings sont conservés, et
aucun échec technique ne sera nommé une obstruction de parité.

La réussite de cet audit certifierait seulement les identités auxiliaires
réellement lues dans FINAL3/4. La sémantique actuelle ne ferme ni Gamma_rank
ni les sommes longues ni D_N. Aucun PASS routinier, aucune réexécution de
banque et aucun autre Lean historique ne sont autorisés.
