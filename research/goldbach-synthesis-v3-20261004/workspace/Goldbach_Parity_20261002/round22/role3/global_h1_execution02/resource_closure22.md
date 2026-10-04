# Clôture du calcul unique — limite mur, catalogue incomplet

Le controller02 autorisé a terminé réellement avec exit1 : `GLOBAL_THERMAL_ATTEMPT_FAIL`, cause `MAX_WALL_SECONDS`. L'enfant unique a démarré au2026-10-03T13:03:11.937646UTC et a été arrêté au2026-10-03T14:03:12.036502UTC. Le contrôleur a écrit sa FIN au14:03:19.496679UTC après sa vérification d'intégrité. Session97614 close, reçu réel968c95. Aucun retry, changement de paramètres ou nouvelle évaluation n'a eu lieu.

Les gardes étaient3600 secondes mur enfant et2147483648 octets d'artefacts. Le reçu rapporte248735870 octets, donc la limite de volume n'a pas été atteinte. Le dernier checkpoint complet du log est86400/204800 nœuds, côté droit/cercle107, à3594.844s au14:03:06.936754UTC. Le fichier de sortie contient86507 lignes, dont la dernière est un enregistrement JSON complet portant la clé `[vertical,right,108,106]`. Ce comptage et cette clé sont des lectures de métadonnées ; les valeurs d'enclosures de ces lignes n'ont pas été réévaluées, ni validées comme un catalogue global complet.

Le catalogue vertical reste incomplet. Arch et les999999 certificats arithmétiques n'ont pas été produits. Le dossier numeric_data contient uniquement new_nodes.ndjson. Ni résultat global, ni résultat du checker structurel, ni child_FIN n'existe. Aucun E_total, accord sous tau, séparation des mutants ou verdict global n'est observé. Les valeurs partielles ne sont pas un oracle pour un prochain calcul.

Cette clôture est un échec de ressource. Elle ne démontre pas que l'identité thermique ou un majorant soit faux et ne constitue pas une réfutation analytique ou une obstruction de parité. Elle n'accorde aucun PASS, certificat de primitives, preuve Lean ou victoire. H1/C5 global, volet horizontal, coefficient additif N et D_N restent ouverts.

## Conservation vérifiée en lecture seule

Les1003 inputs et les1005 captures PREEXEC ont été rehachés. Les2008 lignes d'inventaire POSTEXEC ont été comparées aux octets actuels, toutes intactes. Les3089 fichiers du registre historique ont également été rehachés, sans changement ; registre SHA875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99. Les trois outputs du reçu ont les tailles et SHA attendus. La préparation, la gate, le contexte et les archives sont déclarés intacts par PRE/POST ; les vérifications propres de copies/inputs/archives/outputs confirment ces inventaires.

Lectures : FIN et receipt FULLd55089 ; stdout FULL en deux fenêtres2341c0(lignes1–60) et884dba(lignes61–109) ; stderr vide FULLd55089. PRE/POST sont des inventaires parsés et vérifiés, pas des lectures FULL de prose : projectionc09d97, vérification totale des inputs/capturescda5cf ; archives et métadonnées des nœudscb507a ; clé finale et hachages7d3584. Une première projection2b220e a rencontré une valeur null de type metadata ; la projectionc09d97 l'a correctement traitée, sans réexécution du calcul.

Hachages immuables :

- START7ccb60ee859d294902753afbb0cc939d5f5911d0c1ed7f81a3cef2c488d15683 ; child_START119fa6abf5b4783c5fa0f8dec7322eb6aafdc125e2beeebf5eb181902413d730.
- PREEXECb3734e005f391ddeef49c2342a8775218640c2c0e42e9146077008bb47dda4e3 ; POSTEXEC3465bc934e6cab3dd204c3d0f3a939704a392b0beac32f123b081f3c6199eacf.
- FIN et receipt2827054b4690eee57de7c36095c8babf6f235b8174470462ccfbcb7f90dd3e93.
- stdout552ac9962f9e7fac774b5f3108fc459f0872c9b6ae1cc4353a8c16c0317021e8 ; stderr videe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
- new_nodes.ndjson,199924454 octets :71de0fa2625010240a9bbe249474ca58ba5d0c4a961ed3786026160b087d3c3b.

Les sources du candidat performance_sourcepack02 restent distinctes et non exécutées. Une durée différente pour un contrat futur devra être un addendum neuf, soumis à revue et à une nouvelle gate ; la limite3600s et le reçu du présent calcul restent immuables.
