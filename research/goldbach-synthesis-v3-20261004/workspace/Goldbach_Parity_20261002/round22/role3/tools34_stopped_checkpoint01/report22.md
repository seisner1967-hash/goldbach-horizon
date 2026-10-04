# Outils 34 partiels conservés après le véritable échec 33

Statut : DRAFT_STOPPED_WITHOUT_PREPARATION. Aucun fichier du lot 34 n'est modifié par ce constat. Les quatre copies scientifiques/catalogues sont byte-identiques à leurs sources gelées ; les deux outils sont des brouillons non relus intégralement et ne sont pas déclarés PREPARED.

Le constat metadata `bf09ea`, à 2026-10-04T02:40:33.9378169Z, relève exactement six fichiers dans `round22/judge5/batch34` :

| Fichier relatif au lot 34 | Octets | SHA-256 | État |
| --- | ---: | --- | --- |
| prepare_metadata.py | 34954 | f3d8a404abdc11bd852e711e966c1df80b289bbbcef0f0854f6e909d69fcd94e | DRAFT arrêté ; lecture BYTES_SHA seulement |
| run_once.py | 14362 | dd64c49467b7969c052d7e70fa59f78139372f7a81147c72a0ef67bbb7484bb3 | DRAFT arrêté ; lecture BYTES_SHA seulement |
| source_catalog_elambda_author22.json | 1713 | f094c54a6a10aa0ad026dce78233f98e53d972341e2f2ce08d86306492e330ea | Copie scientifique gelée |
| source_catalog_geometry_author22.json | 4271 | 6f85beb2fd6eaf111a2ef453614938081385456a7d567bfb3e0f39b61e371312 | Copie scientifique gelée |
| sources/ComplexGammaCircleGeometry22.lean | 12002 | 2322915060c608e58c499af0c9303d3032f488e12980bc240aa7eca0807c44c5 | Copie SOURCE ; aucun PASS |
| sources/ComplexGammaMellinLambdaTail22.lean | 11335 | 68a008f55e1dcff723dfcbf398061a69e3c3495fee739965f3cfdc884232b01e | Copie SOURCE ; aucun PASS |

Les sources/catalogues originaux avaient été lus FULL `065dbf`/`bc823b` pendant l'écriture autorisée des outils. Le présent inventaire est BYTES_SHA_METADATA ; il ne prétend pas une nouvelle lecture FULL des deux brouillons.

La création des copies a suivi le véritable FIN de PREP33 : session10814, chunk8ab07f, exit0, FIN 02:29:22.4421470Z. Les copies ont été constatées à 02:31:11.3610741Z (`a9e5a8`). Aucune préparation 34, import-closure, readonly_oleans, invocation de builder, launcher, compilateur, candidat ou banc n'a eu lieu. Il n'existe ni prepared_receipt.json ni batch34_attempt01, et aucun document de gel final n'avait été créé dans le lot 34.

La sélection scientifique 34 exigeait une observation future du module principal 33 entièrement PASS. Cette condition est définitivement non satisfaite pour cet ancien lot : l'observation ROOT33, lue FULL `a29cd9`, a pour SHA-256 `0dc5c9b420f62c43269450bad7dda4a5d030ac3893d40d592569aa0d13e1f1eb` et statut INDEPENDENT_BATCH33_FAILED. Elle inscrit zéro nouveau module/déclaration et conserve l'officiel 87 modules / 1458 déclarations. Le diagnostic reçu est un raccord de continuité au cas LambdaCoefficient0 ; aucune réfutation analytique ou de parité n'en découle.

Les outils 34 restent donc arrêtés avec leur condition d'entrée initiale. Aucun assouplissement silencieux, nettoyage ou relance n'est effectué. EΛ16 et Geometry25 restent des sources sélectionnées scientifiquement ; leurs futures validations seront des lots distincts dépendant d'un véritable PASS ultérieur du principal. SOURCE03, revue indépendante et sélection ROOT35 sont encore attendues pour les nouveaux outils 35. L'observation FAILED33 pourra servir de baseline réelle à ce futur lot distinct, sans transformer le lot 33 en PASS.

Portée : conservation locale des six fichiers et lecture de l'observation ROOT. Ce rapport n'effectue pas une nouvelle conservation exhaustive des archives ni une nouvelle adjudication du compilateur. Les sources/essais 33, les anciennes sources et la livraison07 DRAFT restent inchangés. D_N et WIN demeurent ouverts.
