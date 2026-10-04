# PARAMETER_GUARD01 révision02 — clôture réelle auxiliaire

Verdict : PARAMETER_GUARDS_AND_FIVE_LOG_SAMPLES_AUX_PASS, scope PARAMETER_GUARD01_ONLY. Une invocation du parent autorisé02, cf3e25/session93619, a terminé réellement c7f267 exit0. Un enfant/PID33664, zéro retry et zéro ancien replay. Token52062c7b-bd72-41cf-b8e4-83ac639fbc43.

Gate ROOT f2f00ac117694c747fca86e523741a85870e994627a40f8a6791653ba27d3cc8 lue FULLed14ef ; préparationf10fc82a… et revueSOURCE indépendante50240b80… exactement liées. PREEXEC à17:29:47.035182UTC avant START à17:29:47.040182UTC ; SPAWN17:29:47.047774UTC ; FIN17:29:47.213230UTC, exit0, stop/spawn_error null. Le POST est daté17:29:52.047593UTC. Aucun plafond60s ou1MiB n'a été atteint.

Parent réel : Pythoncanonique -I -S -B -X utf8 parameter_guard01_revision02/run_parameter_guard_once22.py. La commande enfant est intégralement capturée dans START : ce même Python et ces mêmes flags lancent PREEXEC_FILES/006_parameter_guard22.py avec PREEXEC_FILES/008_fixed_parameter_log_model22.py comme seul modèle. Aucun modèle original mutable n'est chargé hors de cette copie vérifiée.

Les vrais PRE/START/SPAWN/FIN ont été lus FULL4e9bb0. stdout3502bytes, stderr0bytes, POST et receipt ont été lus FULL6af61d. Tous les champs de portée interdisent explicitement global_NTT, complete_catalogue, coefficient_N, log_primitive_Lean_certified, spectral_H1, D_N et WIN.

## Résultats observés

check_fixed_constants a réellement validé les cinq p={2013265921,2281701377,3221225473,3489660929,3892314113} par divisions entières jusqu'à leur racine, leurs racines d'ordreK=2^27, les inverses de racines etK, les gardes de couvertureCRT/coefficient et la garde tau. Les racines/inverses et compteurs exacts restent dans stdout immuable ; ce ne sont pas des certificats Lean. N=100000000 etS=288230376151711744 ont été vérifiés, sans NTT globale.

Les cinq points32 construits égalent les points40 calculés sur ces arguments, avec les gardes fraîches de deux endpoints40 :

| argument logarithmique | point32=point40 observé |
|---|---|
|2|199786072581291495|
|3|316653433207702182|
|4|399572145162582989|
|99999989|5309399708094640507|
|100000000|5309399739799983627|

Il s'agit d'échantillons de log(argument), sans revendication de primalité de ces cinq arguments. En particulier, le point de log4 ci-dessus ne remplace pas Λ(4)=log(minFac4)=log2. Toutes les puissances de premiers seront une charge de catalogue distincte. Les séries32/40 partagent la même implémentation, donc ces observations ne constituent pas deux validations de primitives indépendantes.

Les quatre rejets sont réellement observés, avec les diagnostics exacts attendus :

| mutation | diagnostic |
|---|---|
|p=K+1=3*44739243|INVALID_MODULAR_PARAMETER_COMPOSITE|
|g=1, racine d'ordre1|ROOT_ORDER_FAILED|
|point32S proposé pourlog2|RECORD_LOW_ENDPOINT_FAILED|
|échelle1 contre garde tau|AUX_TAU_TOO_LARGE|

Les modifications en mémoire ont été restaurées ; le contrôleur l'a vérifié avant son résultat. Aucun nouveau paramètre externe ou rayon libre n'a été employé.

## Conservation et niveau de preuve

La clôture administrative propre fc1ee8 a rehash1005inputs, dix originaux et dix copiesPRE, puis les3089archives : zéro différence. Cela inclut les originaux manifest/review dont l'ancienne gardePOST était absente. Le dossier contient8outputs de premier niveau et10copies, total322309bytes<1048576. L'ancien paquet01, ses998inputs et son préflight restent conservés ; son actual est absent. Aucune réévaluation du modèle n'a été nécessaire pour ce contrôle de bytes.

Reçu réel ace13827d4e7f7d8d022c7be894d397c2ac855f7fd7f14d0eee197b41e126459 ; stdout18702584d0be11ca444e085290033a7bcc076f1ff0a0179e33cb1731e3ea344c ; POST29b18951e99dba5a9a3f24e9081ac0839bf0d4fec0d371916d2a23dbc9d76133 ; conservation0166dafcde79f4da3e1e7def5955b23e74d86e7f3cb8ae0e3371336c2451d107. Les autres hashes sont intégralement liés dans le reçu de clôture.

Le résultat AUX repose sur les primitives rationnelles SOURCE/PAPER et leur invocation effective aux cinq échantillons. Aucun nouveau crédit Lean, aucun certificat des logs de tousn, catalogue complet, NTT/CRT native, coefficientN, transfertH1 ou contrôleD_N n'est accordé. Le paquet SOURCE52 est encore non compilé par cet exécutant et reste intact. Aucun WIN n'est déclaré et aucune nouvelle exécution n'est autorisée par cette clôture.