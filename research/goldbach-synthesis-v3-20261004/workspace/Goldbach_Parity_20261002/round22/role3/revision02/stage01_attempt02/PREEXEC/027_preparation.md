# ROLE3 — révision02 du noyau G0

Statut : PREPARED_SOURCE_ONLY. La tentative stage01_attempt01 a réellement invoqué Lean une fois le 2026-10-03, de 07:02:03.608143 à 07:02:31.313954 UTC, avec exit1 et sans olean. Son original source cd5cb975242aa38d7d118ac9378409c4bfe406d41227371a7006972d1c145053 et son journal 8affa881e01451cff53f978bd16fddddcc1dc4eb83b7fd3cd42c7b6f30f5552a restent gelés. La première autorisation est consommée.

La présente source est une copie distincte, corrigée uniquement dans des étapes d’algèbre et de tactiques : normalisation de la division négative et de one_div ; traitement de l’unique but dérivé après convert ; factorisation explicite de la rationalisation du déficit ; suppression d’une tactique exécutée après fermeture du but ; normalisation de la limite à moins l’infini. L’identité réelle, les définitions, les hypothèses de positivité et les charges d’intégrabilité restent celles du contrat FINAL2. Aucun axiome cible, placeholder, appel de décision natif ou changement de l’énoncé n’est ajouté.

Les cinq sources FINAL2 et la sélection node16.1 gardent leurs lectures FULL et leurs hashes vérifiés par la préparation précédente. Les API locales ont été lues en source, sans sondage Lean supplémentaire. Les noms d’API et les nouveaux gestes tactiques restent à juger sur une prochaine invocation effective. Les annotations sorryAx apparues dans le premier journal sont des produits de l’élaboration échouée, pas des déclarations ajoutées à la source ; aucune preuve n’a été créditée sur cette sortie.

run_revision02_once.py exige un gate root distinct lié au manifest de cette révision, au launcher et aux deux runtimes canoniques. Son unique enfant est EpsteinKernel22 ; sortie neuve dans revision02/stage01_attempt02 ; cwd revision02 ; cache mathlib4.15 inchangé. PREEXEC contient chaque input et sa copie ; START précède l’enfant ; commande, log, exit, olean éventuel, POSTEXEC et reçu sont conservés. Il ne réalise aucun calcul Python et ne rejoue pas le banc numérique réel déjà accepté par root. Aucun retry automatique n’existe.

Commande future fermée jusqu’à autorisation root :

`PythonCanonical -B -X utf8 role3/revision02/run_revision02_once.py --gate C/messages/round22_role3_stage01_attempt02_authorization.json --attempt stage01_attempt02`

Champs exigés du gate : role=ROLE3, node_id=16.1, attempt=stage01_attempt02, stage=G0_KERNEL_REVISION02, authorized=true, numeric_verdict=EPSTEIN_UNFOLDING_AUX_PASS, modules=[EpsteinKernel22], source_manifest_sha256, launcher_sha256, python_sha256, lean_sha256, no_win=true. Ce document ne donne aucune autorisation.

Cette étape reste auxiliaire. Les sources de fenêtre finie et de déroulement infini sont en développement hors de ce gate ; la queue devra être prouvée à partir des déficits aux bords avec toutes les gardes. Diffusion, Mellin, chaleur, coefficient N et majoration D_N restent ouverts. Baseline officielle57modules/942aux inchangée ; aucune victoire revendiquée. Toutes les 33 déclarations explicites du Kernel possèdent leur #print axioms qualifié, à contrôler par le futur Juge indépendant.
