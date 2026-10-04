# Révision02 du parent PARAMETER_GUARD01 — correction SOURCE de conservation

Ancien paquet sibling parameter_guard01 intact : six fichiers et998bindings. Aucun runtime/import/parser/calcul/gate/START : le gap est une observation SOURCE du Juge, pas un échec numérique, analytique ou Lean. Les controller/contract/modèle80718 et tous paramètres restent identiques en bytes.

Le parent révisé vérifie explicitement auPOST sha(manifest)==prep.manifest_sha256 et sha(review)==gate.independent_source_review_sha256. Il ajoute ensuite pour CHAQUE capture deux vérifications : SHA de l'original égale le SHA stocké auPRE, puis SHA de la copie égale ce même SHA. Cela inclut préparation, manifeste, gateROOT, revue indépendante et les sources capturées. Les vérifications attendues contre prep/gate sont donc conservées même si un original avait changé entre son premier test et la capture. Les contrôles déjà existants de inputs/preparation/gate/archives sont conservés.

AuPRE de la capture, le SHA attendu provient explicitement du binding original ou de prep/gate/review déjà sélectionnés, et ne se redéfinit pas depuis un fichier éventuellement modifié. Original et copie doivent tous deux égaler cette attente avant l'enfant ; les attentes en conflit ferment. Ce renforcement exclut un échange de source entre sa première vérification et sa copie.

Le nouveau manifeste inclut aussi les six anciens fichiers comme inputs readonly, et toutes leurs998bindings, avec dédoublonnage exact des paths. Seuls les nouveaux contrôles et le modèle sont capturés pour l'enfant ; l'ancien contrôleur ne peut être sélectionné par accident. La sélection est encore un sibling direct de role4, donc HERE.parents[2] désigne la même racine B. Gate spécifique toujoursabsente et doitlier seulement cette nouvelle préparation après revue du Juge. Une unique invocation future autorisée ne permet aucun replay01.

Le scope reste PARAMETER_GUARD01_ONLY,1child0retry60s1MiB. Aucun NTT globale/coefficientN/H1/D_N/WIN. Noyaux natifs encoreSOURCE_WORK_IN_PROGRESS, hors préparation.
