# ψ révision02 — portée honnête des lectures

Le reçu historique read_scope22.md du dossier parent demeure inchangé. Il
contient les quatre sources initiales FULL, les trois contrats FULL, les
API du cache TARGETED, les recherches de chemins corrigées et la revue
indépendante SOURCE ROLE4. Duplication reste byte-identique. Les sources BetaLimit et Integral ont
uniquement les espaces 0 .. 1 corrigés, sans modification de leurs preuves.

Nouvelles lectures : log Core FULL 09499e, reçu et FIN Core FULL 61387b ;
hashes START/PRE/POST et parsing d'intégrité POST seulement a6c9ff. Aucun
FULL humain de la fermeture du cache, ni de PREEXEC/POSTEXEC volumineux,
n'est revendiqué. Le builder initial a été relu FULL cdaaa3 ; la lecture
groupée fc5126 était tronquée et n'est pas revendiquée FULL.

La correction SOURCE consiste seulement en Function.comp_apply avant simp,
puis notation d'intervalle 0 .. 1. Core révisé a été lu FULL 0de37d,
BetaLimit/Integral/Duplication révisés FULL e0f033, launcher et builder
finaux FULL 8d7993. La recherche 2a2834 ne trouve plus de notation compacte
entre deux chiffres dans les nouvelles sources Lean ; son exit1 est le
résultat normal de rg sans correspondance. Les API n'ont pas changé.
L'inventaire lie leurs bytes sans inventer une lecture FULL.

La revue ROLE4 a84072/41e749 et les API60792f/c40ad1 concernent le paquet
initial ; les preuves analytiques inchangées la conservent, la réparation de notation
reste une nouvelle SOURCE jusqu'au nouveau passage réel du compilateur.

Ce dossier n'a exécuté aucun Lean, probe API, Python math ou banc. La seule
exécution nouvelle autorisable serait le launcher unique sous gate ROOT
distincte, STOPFIRSTFAIL, captures neuves, sans retry.
