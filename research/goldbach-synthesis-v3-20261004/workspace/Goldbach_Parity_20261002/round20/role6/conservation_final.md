# FINAL — préflight de conservation du tour 20

Le nouveau préflight a réellement été exécuté une seule fois après lecture complète des sources et autorisation distincte du coordinateur. Il a terminé avec le code de sortie 0, sans erreur de lancement. Ce résultat porte uniquement sur la conservation des fichiers ; aucun résultat mathématique ni aucune victoire n'est déclaré.

- START réel : `2026-10-03T02:00:39.573868+00:00`.
- FINISH réel : `2026-10-03T02:00:44.673423+00:00`.
- Invocation shell réelle : chunk `3c65e4`, code de sortie 0.
- Autorisation : `ROOT20_CONSERVATION_AUTHORIZED_FULL_SOURCE_READ_CANONICAL_ATTEMPT01`, fichier root SHA `6b6d49d7993e9b9fd20514895453f2ff5c9d6096c7255a8e3ca2df48acd23aef`.
- Avant : inventaire exact de 1 808 fichiers, 1 808 SHA comparés, aucune absence, aucun ajout, aucun changement.
- Après : inventaire exact de 1 808 fichiers, 1 808 SHA comparés, aucune absence, aucun ajout, aucun changement.
- Union historique : 1 361 fichiers hérités, 446 pièces du tour 19 et son contrôleur, soit 1 808.
- Les deux inventaires et tous leurs SHA sont identiques. PDF et ZIP ont seulement été hashés et correspondent aux SHA fixés, avant et après.

Huit captures PREEXEC exactes ont été écrites avant le START : source nouvelle, lanceur nouveau, préparation, autorisation root, registre20, PROBE20, contrôleur19 et carte des SHA originaux. Les commandes, le runtime Python et son SHA, le répertoire et les deux changements d'environnement sont dans le START et le reçu. Tous les fichiers de sortie et captures ont été créés en mode exclusif ; aucune reprise n'a eu lieu.

La source a exclu les répertoires `.git`, `.lake`, `.arbor`, `__pycache__`, `.pytest_cache`, `.mypy_cache`, `.ruff_cache`, le seul `REPORT.md` racine et les répertoires racine `round>=20`. Le répertoire `cache` n'est pas exclu. Les liens inattendus sont refusés. Aucun fichier protégé n'a été écrit. Aucune ancienne source, aucun ancien préflight, aucun producteur numérique, noyau, logarithme, signe, Lean ou traitement du PDF n'a été exécuté.

Les résultats et traces canoniques sont `round20/conservation.json` et `round20/role6/conservation_attempt01_{started,receipt}.json`, avec le log binaire `round20/role6/conservation_attempt01.log`. Le log et le résultat ont chacun leur SHA réel, sans présumer l'égalité de leurs octets. Le reçu a été relu intégralement dans le chunk `b9fb0f` et les résultats stockés ont été lus dans `980373`, sans relancer le préflight.

- START SHA : `6e3922c33a93a09516435ada6cd1dd2549db8d275e54a1393707f9da7805ba24`.
- Reçu SHA : `da9edf5b0c93977369b0f296dfc0fd909e0c57f0bc7f344a1446fa46f83e359a`.
- Log SHA : `98210229bb15abd9675bbfe27152ab7c2ea4babe9f0b3f9fdafa144745ccd8c2`.
- Résultat SHA : `d36eeaccb6c7c3809569e0a519ae69227b0381c37a078351c6a93b96ec14539a`.

Le reçu FINAL gèle les 17 fichiers nouveaux de ce préflight. Le rôle6 attend une sélection20 et une nouvelle autorisation numérique distincte avant de préparer ou lancer les futures banques mathématiques à N=10^8. Le cumul des théorèmes et modules acquis n'est pas modifié par ce préflight.
