# ROLE5 — BORD04, revue SOURCE indépendante

**SOURCE cohérente ; aucun PASS présumé.** La seule correction supprime `rw [← inv_pow]` dans `angularCharacter_pi`. Le vrai FAIL24 cherchait `(a^n)⁻¹` alors que le but était déjà `(-1)⁻¹ ^ N = (-1)^N` ; le `norm_num` préexistant demeure. Comparaison textuelle exacte `76d6aa` : nouveau fichier = ancien fichier avec cette seule ligne retirée. Aucun autre corps, énoncé, domaine, nom ou impression n'a changé. Aucun nouveau déficit logique précis identifié ; l'élaboration reste à effectuer dans un lot distinct.

Paquet auteur gelé : `D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/angular_mellin_border_source04`.

| Fichier | SHA256 | Lecture propre |
|---|---|---|
| AngularMellinBorder22.lean | 601a3360ff92f9bb1f7ecc64bc0754f2bb2a703cf143ff00f16d3b5bec6be2c4 | FULL ed8a4b, 13323 octets |
| source_contract22.md | 0c9c52a847a51bd6585cc48811a14ea01895a2e8771ed129b125b271d794d3af | FULL 38a5c2, hash 180fed |
| source_catalog22.json | 6fba207298fd4caf7466358febad9364daf7f69110be9b48862b5481cd2a2a21 | FULL 38a5c2, hash 180fed |
| source_read_receipts22.json | 85fdba1a02cb01b7b899477e5d0cc7054620388e369eeefa00cb20b959c81935 | FULL 180fed |
| source_handoff22.json | 55c3055d0b8ce81fe47f92d7df2ff6d37759b59826fbd8ce324b36961b027053 | FULL 180fed |

30 déclarations et 30 impressions qualifiées, inventaire textuel conservé : 22 théorèmes et 8 définitions, zéro import local. Les axiomes de ce nouveau fichier ne sont pas encore compilés. Les 26 impressions standards du lot24 ne lui donnent aucun crédit partiel.

La portée mathématique reste celle des revues23/24 : a>0 assure Re(a−iθ)>0, slitPlane et non-annulation de la base de la puissance principale, pour q complexe arbitraire. Les dérivées du cpow, du caractère et du produit sont construites, puis la continuité et les intégrabilités avec volume sur [−π,π], puis FTC. Les caractères aux deux bords valent (−1)^N ; aucune périodicité du cpow n'est supposée. Pour N>0, l'identité est J(a,N,q)=B(a,N,q)+(q/N)J(a,N,q+1), avec B=i(−1)^N[(a−iπ)^−q−(a+iπ)^−q]/(2πN). B=0 à q=0 ; B=−(−1)^N/[N(a²+π²)]≠0 à q=1. La non-annulation n'est pas universelle en q. Aucune dérivée, intégrabilité ou identité finale n'est offerte en prémisse.

Vrai ancien source03 1fa9de9a41a432b3745d1dce719018452e6f8f9b183bb9635d07191f1dcf91da et log24 45c7c8475eed1e407b3405259227b0937a9beb8bfe7e6f3ddcc843179171c46b sont conservés. Lecture du diagnostic24 TARGETED lignes initiales `76d6aa`, log complet propre antérieur `4623b2`, receipt complet `50889c`. La sortie du hash-table contract/catalogue38a5c2 masquait les hashes à l'affichage ; leur projection explicite180fed les vérifie. Les API primaires ciblées déjà lues des revues23/24 sont réutilisées comme sources documentaires ; aucune sonde ni ancienne compilation n'est rejouée.

Cette revue SOURCE ne crée aucun PREP, gate, invocation Lean, import candidat, calcul numérique ou olean. Baseline ROOT observée82/1367, inchangée. Les outils futurs batch25 ne porteront que ce module30, avec cache Mathlib/Init/Prelude readonly et répertoire local de dépendances vide. Il faudra une autorisation ROOT de préparation metadata, puis une gate Lean distincte. Mellin37 est revu séparément et n'est pas une dépendance de BORD. Trace globale, uniformité de phase, correction des puissances premières, frontière positive, D_N et WIN restent ouverts.
