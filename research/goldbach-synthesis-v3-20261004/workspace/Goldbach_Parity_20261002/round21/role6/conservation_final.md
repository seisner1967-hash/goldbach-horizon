# Conservation21 — tentative nouvelle unique, métadonnées seulement

**PASS_EXACT_CONSERVATION**, code réel zéro et crédit de conservation accepté. Il ne s'agit ni d'un banc arithmétique, ni d'une compilation Lean, ni d'un résultat mathématique. Aucune victoire n'est revendiquée.

Le registre de la boucle21 contient exactement **3028** chemins et empreintes : **1808** antérieurs, **1219** pièces de la boucle20 et son contrôleur. Deux inventaires indépendants, avant puis après la lecture des bytes, retrouvent chacun ces3028 fichiers. Chaque observation vérifie leurs3028 empreintes, sans fichier absent, supplémentaire ou modifié. Les noms et empreintes sont identiques entre les deux observations.

Les deux originaux ont été lus uniquement pour SHA256. PDF : `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24` ; ZIP : `32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd`. Leurs empreintes attendues et observées sont égales avant et après ; `INPUT_HASHES.json` est conforme. Aucun PDF n'a été extrait ni rendu.

## Exécution réellement autorisée

La source, le lanceur et la préparation ont été préparés puis gelés avant la revue complète du coordinateur. Le seul acteur a exécuté le lanceur après l'autorisation distincte `round21_conservation_authorization.json`, SHA `0ea14a4f47058f38817fd975a2e5b2d7a1b95d2e0940b66ae57c90e63c6189f7`. L'invocation des outils porte le reçu `1cb839`, exit0.

- START réel : `2026-10-03T05:18:32.248223+00:00`.
- FIN réelle : `2026-10-03T05:18:40.795646+00:00`.
- Runtime connu : Python à `C:/Users/Utilisateur/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe`, SHA `4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c`.
- Commande enfant réellement exécutée : Python, `-B`, `-X`, `utf8`, `round21/role6/conservation_attempt01_source_PREEXEC.py.txt`, avec cwd `round21`.
- Huit copies intégrales PREEXEC : source, lanceur, préparation, autorisation, registre, PROBE, contrôleur20, `INPUT_HASHES.json`. Elles ne sont pas des copies créées après l'exécution.
- Deux reçus supplémentaires PREEXEC enregistrent les empreintes, tailles et chemins du runtime et des originaux, sans copier ces binaires.
- Le contrôle POST observe23 chemins : entrées, copies, runtime, originaux et reçus START/réservation. Aucun n'a changé. Les empreintes attendues des reçus sont fixées avant l'enfant ; un exit0 ne créditerait pas une altération.

## Empreintes des pièces principales

| Pièce | SHA256 |
|---|---|
| `round21/conservation.py` | `ab4495d95052c8e64253a1c4e93726799c36f7c0418217dd9c599d24d72d54c2` |
| `role6/run_conservation_once.py` | `5cba3b716cf510490243722f60de50e87899d1014cef70d5af1eade4849c45a4` |
| `role6/preparation.json` | `f7419bbfbe7c902ac87ddaa8065d2f4f351fd89fdd94196c99acb6c8f1175a73` |
| `previous_artifacts_sha256.json` | `5c1c372a2a723a1a06224c6531c2e0775978bbe902f02cf910450a583772896c` |
| `PROBE_BLOCK.md` | `015cccf57d59c53abd34f4b6623b891199fdb61a9f8acafcd4f352df0b8fd7de` |
| `round20/controller_manifest.json` | `815d2ce77851a01d9addfa4202a17edb787a42f7f080d4e41cab18aa7b002b04` |
| `role6/conservation_attempt01_started.json` | `cc352208c816fa00a77d40f3d0ed43c6af46b217f53c9a18993c993f1532e6af` |
| `role6/conservation_attempt01.log` | `9fef6095f1e90439c9bd16ae1bcc97ef642b304305d9b0c21d328ffd6c00be7a` |
| `conservation.json` | `51211ade1ad6cc490e724637c1e0d4602a3f184e46dd971eb6c282892e63208f` |
| `role6/conservation_attempt01_post_integrity.json` | `e8f228a9e014ae3f72a1d49da33e5fc5be2691f63d10d80e944a4274bb04bcf6` |
| `role6/conservation_attempt01_receipt.json` | `c23ac6570207f0e27131375d97867363c12d5df58cfb19b87f158ac326a492fa` |

L'inventaire exclut le rapport mutable racine, `.arbor`, `.git`, `.lake`, les répertoires de caches explicitement nommés et les boucles de rang au moins21. Aucun chemin du registre gelé n'est masqué par ces exclusions : cette compatibilité est vérifiée avant les observations.

Les ajustements statiques du lanceur ont précédé PREPARED et toute invocation : attentes POST fixées avant l'enfant et conservation d'une erreur de lecture du résultat. Ils ne sont pas des échecs d'exécution. Le seul préflight conserve son START, ses captures, son log et son code de sortie. Zéro ancien préflight, producteur, calcul de signes/logarithmes, noyau, banc ou audit Lean a été rejoué. Aucun des3028 fichiers protégés n'a été écrit.

Cette étape de conservation est close. ROLE6 n'a exécuté aucun banc mathématique21 ; un contrat nouveau sélectionné et une autorisation distincte seront nécessaires pour cela.
