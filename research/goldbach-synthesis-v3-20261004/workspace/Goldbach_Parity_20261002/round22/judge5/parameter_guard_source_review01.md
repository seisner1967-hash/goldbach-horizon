# PARAMETER_GUARD01 — revue indépendante SOURCE, aucun banc

Reviewer ROLE5, auteur ROLE4. Statut **SOURCE_REVIEW_OPEN_CONSERVATION_REPAIR_REQUIRED**. Mathématique papier des gardes cohérente ; aucun import/exécution du modèle, aucune sonde, aucune NTT ou compilation. Ce rapport ne constitue ni gate ni AUX_PASS.

Racine auteur : `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role4\parameter_guard01`.

| Fichier | SHA256 | Lecture propre |
|---|---|---|
| parameter_guard22.py | 3cf9b27e50aa196aacd9e78f6093c2f6741f75af21414206b9b0bdf1c5684396 | FULL021fb9 |
| run_parameter_guard_once22.py | c093bd5b4b5652d3ebde82820a8da45a084ae54583dbbc9531b2b6d257c846ac | FULL2c7026 |
| contract22.md | a9366f53f0939a0d3e6bae1b54766027cddb01a17e8b268494f5452c08dc50ff | FULL0ecfb3 |
| preparation22.json | 418654b335c4e26043b1262eb371a2517e3bcde39db470190f5a25320a88a3bc | FULL0ecfb3 |
| read_receipts22.json | 4120755a50dc1ee63e0736d58a64a7ad0910ba4d8b66b342a29a17534fb523c8 | FULL1bde0f |
| prepared_manifest22.json | 6e9db8525d2467c941fdc0dad85ccd5bcec7556fa49cf0368ef4052e223018d2 | HEADER/capture projection1bde0f ; tous998bindings et bytes479036 |

Le modèle immuable `role4/circle_ntt_paper01/fixed_parameter_log_model22.py`, SHA80718ee9c1306a974554a70322ad36648897216890f6747ed2ddede840421d98, a été relu FULL0f013d, auparavant FULL7d5261 dans la revue NTT indépendante. Aucun de ses corps n'a été appelé. Metadata479036 vérifie exactement998paths uniques sans différence :972runtime natif/std,19inputs PAPER,1handoff,1ancienne revue indépendante,4nouveaux contrôles,1registre3089. Le manifeste est haché entièrement et projeté honnêtement, sans faux FULL de son texte ni de chaque runtime.

## Gardes et domaines effectivement écrits

N=100000000, K=2^27 et S=2^58 sont fixés dans enfant et modèle. Les cinq moduli/racines candidats restent les cinq paramètres du contrat NTT. Chaque primalité est prévue par divisions exhaustives jusqu'à sqrt(p), sans primalité supposée ou Miller-Rabin heuristique ; omega^K=1 et omega^(K/2)≠1 donnent exactement l'ordre K. Euclide paie les inverses, les moduli distincts premiers paient CRT et sa couverture au-delà de la borne entière du coefficient. Ces gardes existent dans SOURCE, leur résultat réel est encore inconnu.

Les cinq arguments {2,3,4,99999989,100000000} sont des entiers dans [2,N], sans assertion de primalité. Le producteur construit réellement chaque point32 par série rationnelle32, arrondi médian tie-to-even et clamp ; la vérification recalcule la boîte40 sans rayon fourni ; un point40 frais est également construit. Les deux points doivent différer d'au plus2 unités d'échelle. La validité mathématique des séries/endpoints demeure PAPER, distincte de leur future évaluation et de leur future formalisation Lean. L'appel constructeur32 présent dans cet enfant satisfait la construction canonique pour ces cinq points seulement ; le checker40 isolé certifie un enclosure, pas cette canonicalité pour un catalogue complet.

Les quatre mutants sont discriminants sur papier et les diagnostics attendus correspondent aux gardes : K+1=3*44739243 échoue au diviseur3 ; g=1 échoue à l'ordreK ; le point32*S pour log2 échoue à RECORD_LOW_ENDPOINT_FAILED ; scale1 échoue à la comparaison entière du tau. Les mutations de MODULI sont restaurées par finally et contrôlées à la fin. Tous ces rejets restent attendus, jamais observés.

## Launcher et déficit exact avant gate

Un seul futur enfant Python canonique -I -S -B -X utf8, exécutant les copies PREEXEC du contrôleur et du modèle haché, au plus60s, zéroretry ; stdout/stderr séparés et PID/START/FIN/PRE/POST/reçu. Un second essai est empêché par mkdir exclusif. La limite de tentative1MiB réserve512KiB aux captures et64KiB aux métadonnées ; le JSON enfant est borné32KiB. La cadence de surveillance n'est pas une mesure de performance. Ni catalogue complet, NTT native ni coefficientN sont calculés dans le contrôleur.

**Déficit documentaire précis :** au POST, la boucle rehash les998bindings, le registre/archives, PREPARATION, GATE et les copies capturées. Les originaux du manifeste et de la nouvelle revue indépendante sont des contrôles ajoutés hors998bindings. Ils ne sont pas rehashés au POST ; comparer seulement la copie à son ancien digest ne démontre pas leur conservation originale. Le manifeste lui-même est bien absent des bindings (479036). Une révision distincte doit vérifier `sha(manifest)==prep['manifest_sha256']` et `sha(review)==gate['independent_source_review_sha256']` au POST, ou vérifier original **et** copie de chaque captured contre son digest. Les archives et998bindings restent correctement vérifiés dans la SOURCE actuelle.

Aucun autre défaut mathématique/API précis détecté. Ne pas ouvrir la gate sur cette version tant que ce raccord de conservation requis n'est pas réparé et revu. Les sources/préparation actuelles sont préservées ; ROLE5 ne les modifie pas. Après réparation, un futur AUX_PASS porterait seulement sur ces constantes et cinq échantillons sous les primitives PAPER auditées. Il ne paierait pas les log de tousn, leur certificat Lean, les noyaux NTT/DIT/DIF, le coefficientN à10^8, H1 uniforme, PP/frontière, D_N ou WIN.
