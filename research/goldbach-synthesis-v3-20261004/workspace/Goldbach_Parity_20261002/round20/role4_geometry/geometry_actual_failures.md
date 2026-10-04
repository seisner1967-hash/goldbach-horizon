# Géométrie20 — échecs réellement observés sous gate

Gate root distincte : `round20_source_geometry_authorization.json`, SHA `03c97de5c89feee39a9ad599427e14e4239f75025ba6eb85e375036ab1710549`. Seul `compile_once.py` v2 gelé, SHA `ac1b9f2e3426a1ca9c311d3d6481b4a102bed6a3ac125ec404f214b47e58baff`, a lancé la nouvelle source. Aucun ancien module/PASS n’a été ciblé ; aucun Python mathématique.

## Tentative01 — FAIL exit1, aucun crédit

- START original `2026-10-03T05:59:30.148992+02:00`, FIN original `2026-10-03T06:00:25.216355+02:00`, soit `03:59:30.148992` à `04:00:25.216355 UTC`. Les receipts originaux sont conservés sans réécrire leur fuseau.
- Source PREEXEC : `attempt01_source_PREEXEC.lean.txt`, SHA `22bb640570931e2d7ad2575347d6b5099270dda4680e3d7472939d4f20449d13`, exactement la première source relue/autorisée.
- START : `attempt01_started.json`, SHA `cad2d5f3d6b66c2fdf2ec23e748455061efad5dfaf850f656a6dc054eb5a3f6f`.
- Receipt de sortie brute avant postchecks : `attempt01_finished_raw.json`, SHA `934dfb80012ba34b0abd916304299333c3df77ff3790d182ab84a39464707a63`.
- [Log FULL](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/attempt01.log), lu dans `09cf2c`, SHA `bf99572717dc777c978948d68cc0dbda4ad0da37fd71bb6e967bca7fe75bab07`. Subprocess réel exit1 ; `credited_pass=false`, `post_integrity.all_unchanged=true`, aucune liaison échouée, aucun olean produit.

L’unique diagnostic est à la ligne147 de la source PREEXEC :

```text
after simplification has type Real.log 2 <= 2 - 1
but is expected to have type Real.log 2 <= 1
```

Le helper `htwo` emploie `simpa using Real.log_le_sub_one_of_pos ...`. La simplification ordinaire ne normalise pas la soustraction de numéraux réels dans ce contexte. L’inégalité mathématique est exactement la même ; le défaut est une fermeture tactique, sans hypothèse nouvelle ou défaut mathématique démontré. Aucun aveuglement de parité n’intervient ici.

`#print axioms` affiche `sorryAx` pour `source_logY_four`, `source_sigma_pos`, `source_sigma_le_quarter`, `source_geometry` et les trois wrappers source qui dépendent du théorème raté. C’est la propagation des objectifs échoués du compilateur. Les autres impressions n’affichent que `propext`, `Classical.choice`, `Quot.sound`. Tout le module reste non validé et sans crédit.

Réparation autorisée après cet exit1 réel : remplacer uniquement le `simpa` fautif par une chaîne `calc` concluant `(2:Real)-1=1` avec `norm_num`. Énoncés, seuil `u>=10^24`, gardes, imports, gate, lanceur, préparation, rapport gelé et toutes les entrées restent identiques. La tentative suivante doit employer la source ainsi modifiée ; aucun rejeu du FAIL inchangé.

## Clôture réelle — tentative02 PASS, aucune autre erreur

La réparation décrite est l’unique changement de la source. La nouvelle source et son snapshot02 portent le SHA `bc249b736e460716cccc7e8a9f9ccab9ac508133c8664bd6278795bd3dcb890a`.

- START original `2026-10-03T06:02:08.949583+02:00`, FIN original `2026-10-03T06:03:03.232369+02:00`, soit `04:02:08.949583` à `04:03:03.232369 UTC`.
- `attempt02_started.json` : `c15542195bb8ec6ee3dfe44027f37ccfce705573226d01e1597bca628c4830af`.
- `attempt02_finished_raw.json` : `b3ef33b3ca377d47e0c83329b4a95efe22af8a064de556e32eced91738f955f2`.
- [Log02 FULL](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4_geometry/attempt02.log), lu dans `643632` : `1a79f4d6f234151eb6ecbd86bce261a3d89ea50856647d686602af2500f2de4d`.
- Ledger final `geometry_build_receipt.json` : `dee0fca8a69ce57490d70fd36f9bcab149caad91613655581b807d77cec424de`.
- Olean publié `FriableSourceGeometry.olean` : `a18d92c97badf4ddb7ebff9c96b1367114c3748b99d7dc09558e4bfd565044b3`.

Exit compiler réel0, `credited_pass=true`, `post_integrity.all_unchanged=true` sur **104 contrôles**, zéro liaison échouée. Les 62 impressions d’axiomes n’affichent que `[propext, Classical.choice, Quot.sound]`, aucun `sorryAx`, aucune erreur ni warning. La preuve de `source_logY_four` et tous ses dépendants sont maintenant validés dans ce module.

Clôture : exactement deux invocations fraîches, un FAIL de normalisation réel puis un PASS après modification de source. Aucun FAIL mathématique/parité n’a été observé. Aucun rejeu de PASS ou FAIL inchangé, aucun ancien source compilé, aucun Python mathématique. La source PASS, l’olean et les receipts sont gelés ; aucune nouvelle invocation de géométrie n’est prévue.
