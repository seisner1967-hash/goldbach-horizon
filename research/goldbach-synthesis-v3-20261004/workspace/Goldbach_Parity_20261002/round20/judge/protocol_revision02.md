# Révision statique02 du schéma numérique, avant toute exécution Juge

La préparation01 et son reçu metadata sont archivés avec le suffixe
`NOT_EXECUTED`. `audit_v01_NOT_EXECUTED.py.txt` conserve la source initiale.
Aucun START Juge, audit, Lean, producteur ou nouveau calcul numérique n'a existé.
La lecture metadata7b755d des clés JSON a détecté que N n'est pas top-level.
La lecture9825fe confirme les chemins réels ; l'affichage des grands paramètres
friables a été tronqué, sans prétention de lecture FULL de leurs rationnels.

L'unique correction de code audit est dans `stored_numeric` : lire N dans
`parameters_and_source_guards` pour friable et dans `parameters` pour composite ;
lire les gardes dans le champ imbriqué du premier et dans `source_guards` du
second. Les statuts, exits, hashes et tous les objets sont inchangés. Aucun log,
signe, rational, factorisation, noyau ou producteur n'est recalculé.

Le lanceur retourne1 si un binding change après le subprocess, même si le child
est sorti0 ; RAW exit et log restent conservés, `credited_pass` devient false.
Cette correction du lanceur avait été apportée avant le gel initial metadata.

La préparation02 est une nouvelle fixation metadata de hashes après correction
statique. L'autorisation ROOT20_JUDGE_AUTHORIZED distincte demeure obligatoire.
