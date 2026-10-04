# Agent 5 — Juge indépendant, boucle 9

**Verdict : `PARTIAL_PAYMENTS_WITH_OPEN_PRIME_SIGNED_MOMENT`. Victoire : fausse. Score sémantique : 0.** Le rejeu indépendant du nouveau banc et de la page source 27 réussit, avec conservation des 307 artefacts antérieurs. Les identités corrigées sont exactes dans leurs domaines déclarés. Deux paiements analytiques écrits sont disponibles, mais le contrôle signé du premier axe premier, le terme couvert `2 max(e,0)` et la calibration effective BV de la bande physique restent ouverts. Aucun nouveau candidat Lean gagnant n'a été soumis : `lean_invoked=false`, aucun code de sortie du compilateur, aucun nouveau module ni théorème. Le compteur historique reste neuf modules auxiliaires et 116 conclusions.

## 1. Gel définitif et reproduction

Le gel a été effectué après le signal explicite de fin du rôle 3, à l'empreinte `491b72cb88aa1f2d55c5c65ce725e845b41d478a152ed4166697aadd84c7ec2d`. Les cinq rapports de rôle ont été lus intégralement, ainsi que `PROBE_BLOCK.md`, la clarification de (54), le renderer et les sources numériques. Le manifeste `judge/input_sha256.json` lie les cinq rapports, le seul nouveau script, son JSON, ses helpers locaux, le registre, la clarification, le renderer, les rendus et le PDF original. Les helpers historiques importés par le banc sont également vérifiés par leurs empreintes dans le reçu et dans le registre ; leurs anciens bancs ne sont pas relancés.

Commande complète de reproduction, exécutée avec code de sortie 0 :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round9\judge\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

Le builder contrôle les empreintes avant et après les opérations, s'arrête sur tout code de sortie non nul et refuse un nouveau fichier `.lean` dans round9. Le helper `judge/verify-frozen.ps1` charge explicitement le helper de conservation de round9 : il vérifie les 307 empreintes, dont 54 fichiers de round8, et contrôle les ajouts éventuels aux inventaires antérieurs. PNG et `.olean` sont inclus. Le baseline reste `4a637dc44cd1fe2d7ae5850b4999ab052c069084143d69aa52484f66e250fe0f` avant et après.

Le seul banc relancé est `new_contract_checks.py`, avec ses sorties isolées dans `judge/numerical`. Tous les champs du JSON, sans exclusion, et tous ses octets sont identiques à la production : `PASS_EXACT_REPLAY`. Le manifeste d'entrée a l'empreinte `8719737073aa1e7616d330da245f1d92aa9c1e22974ec5de42f2e90a77521e74`. Le reçu détaillé est `judge/judge_receipt.json` ; le sous-reçu est `judge/numerical/replay_receipt.json`.

## 2. Statuts numériques conservés séparément

| Contrat | Statut exact conservé | Portée |
|---|---|---|
| Transport corrigé V2 | `PASS_IDENTITY_ONLY_CORRECTED_V2` | Douze points et préfixe `m=1..1024`, à `N=100000000` ; aucune énumération de la queue |
| Énergie pondérée | `PASS_IDENTITY_ONLY_WEIGHTED_ENERGY` | `J={3,7,11,13}`, `m={303,311,323,658911,112211}`, `alpha=100`, `H=1000` |
| Masque omis dans V1 | `ERROR_FALSIFIER` | `n=2`, `m=99999998`, `r=161`, `k=621118` |
| Affirmation de primalité pour `m=311` | `ERROR_FALSIFIER` | `N-m=113*199*4447`, donc Mangoldt nul malgré un raw actif |

Le statut général reste `FINITE_NEW_CONTRACT_CHECKS_ONLY`. Ces statuts ne sont pas fusionnés en un PASS quantitatif. Le reçu annonce `properpower_analytic_payment_tested=false`, `analytic_gain=false`, `rank_one_assumed=false`, aucune victoire et aucun appel Lean.

V1 est fausse parce que `gcd(r,kN)=1` n'entraîne pas `gcd(k,N)=1`. Au témoin ci-dessus, `gcd(k,N)=2` : la formule omet l'unité de `k` et ajoute `log(2) log(161)` tandis que `Lambda_N(2)=0`. V2 conserve soit `Lambda_N` et la coprimalité de `k,r`, soit Mangoldt ordinaire avec les deux unités explicites. Le rejet de V1 est une falsification arithmétique avant compilation ; aucune erreur Lean n'est fabriquée.

Pour `m=311`, l'affirmation de primalité du premier axe est concrètement fausse. Le passage corrigé vers l'opérateur conserve le poids Mangoldt nul. Ces deux falsifications rejettent des raccourcis déterminés ; elles ne constituent pas une impossibilité générale de compensation.

## 3. Source (54) relue et reproduite indépendamment

Le PDF original conserve son empreinte `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24`. Sa page physique 27 a été examinée visuellement. Le renderer indépendant produit dans `judge/source_pages` les mêmes pixels PNG, le même texte extrait et le même reçu, avec égalité des octets et des empreintes : PNG `890eef47a566adb22c7ef10a9f5594e19c9c84dc4499bac38efe714910660c1e`, texte `8715816a60891819cc02534ee6f0df68d1f49df5e9f6bd855f8895f2c65a8a56`, reçu `7401abfbb91eed0c9eca503ade085656efb308ac75e0a5c52a674c3d88a850a8`.

La source porte exactement

```text
u (|W_K(R)+H_K(0)| + u |A_K(R)|)
 <= 4*10^8*u^5*exp(-sqrt(u/60)) + 160*u^2*exp(-u/40),
K <= N^3, R >= N^(1/5), u >= 10^6.
```

Le facteur employé dans le majorant de J3 est `exp(-sqrt(u)/60)`. Il est volontairement plus grand, donc valable comme affaiblissement ; il ne doit pas être cité comme transcription littérale de (54). Pour `K` pair, le principal est `H_K(0)=S(K)`. Le préfixe vide reste traité directement, sans lui attribuer un principal fictif. L'onset adaptatif du contrat source demeure `u>=10^24` ; aucun ancien document n'est réécrit.

## 4. Paiements écrits et portée quantitative

Le transport exact J1/J2 garde les caps, unités et fronts stricts du cadre source. Le paramètre auxiliaire `a9=ceil(N^(7/16))` change la face dans les deux noyaux ; il ne remplace ni l'alpha source ni le Q source dans le déficit initial. La cancellation de `k=1` s'effectue conjointement dans physique et modèle.

J3 paie le défaut harmonique. Sur `m>=ceil(N^(3/4))`, les deux préfixes entiers sont au moins `N^(1/5)` sous leurs prémisses explicites, avec le même `K=(N-m)N`, son masque réel et ses endpoints. Les deux principaux `S(K)` s'annulent. La petite face est payée directement. La marge écrite est

```text
E_Z9/N = 8*10^8*u^5*exp(-sqrt(u)/60)
         +320*u^2*exp(-u/40)
         +12*u^2*(1+u)*exp(-u/4).
```

L'audit 3 vérifie les constantes, planchers et décroissances et établit `E_Z9 < 10^(-12) N/(u log u)` pour tout `u>=10^24`. Il s'agit d'un paiement analytique écrit indépendant sous les inputs source, sans certification Lean ni validation par le banc à `N=10^8`.

J4 paie qualitativement la bande physique. Il conserve les fibres coupées, `gcd(d,rN)=1`, les unités, les puissances propres, les queues physique et principale séparées et les endpoints. Sa coupe auxiliaire `B9_aux=floor(N^(1/64))` est distincte du B acquis et du B_cut antérieur. Le niveau est `q<=2N^(15/32)`, avec le facteur 2 ; le BV all-prefix et ses constantes supplémentaires donnent seulement un seuil non évalué. Le résultat `O_A(N/u^A)` écrit ne constitue donc pas une calibration effective de J4 dès `u=10^24`.

W8–W12 paient les puissances propres du premier axe par des majorants positifs explicites : `sum_(k<=Q)1/phi(k)<3(1+u)`, `tau(z)<=2^2040 z^(1/8)` et `sum_(n=p^j,j>=2)Lambda(n)<=sqrt(N)u^2/log 2`. Ils gardent les puissances unitaires du premier axe et donnent la borne

```text
sqrt(N)*u^3/log 2 * [2^2040*N^(1/8)+3(1+u)].
```

L'audit 4 puis le raccord direct de l'audit 3 vérifient que cette borne est au plus `N/(1024 u log u)` dès `u>=65536`. Ce paiement est élémentaire et effectif, sans BV ; il reste une démonstration écrite, non un résultat du test fini ni un théorème Lean.

## 5. Raccord direct au ledger a9, sans double paiement

Le bracket initial de la route W12 est `B_H=P_tail^H-M_alpha`. Le bracket de la route J5 est `B_a9=P^a9-M_a9`, avec le même front `a9` dans ses deux termes. Ces brackets sont différents. Le §7 final de l'audit 3 fournit une nouvelle application directe du majorant positif W11 à `B_pp^a9`, sans supposer une égalité ou une comparaison entre les valeurs signées `B_pp^H` et `B_pp^a9`.

Pour chaque `n=p^j`, les deux masses absolues du bracket a9 sont au plus `u Lambda(n) tau(m)` pour le physique et `u Lambda(n) sum_(k<=Q)1/phi(k)` pour le modèle. Tout front au moins 1 et toute restriction unitaire ne font que réduire ces majorants. Cette uniformité conserve le même cap Q et tous les points actifs. Elle justifie directement le paiement `PP-a9-paid`, sans réintroduire la route H.

Le ledger exact choisi devient donc

```text
D_N = B_prime^a9 + B_pp^a9
      + P_bande^{>=2} + Z_face^{>=2}
      + I_alpha + 2 max(e,0).
```

Le poste `B_pp^a9` reçoit le paiement explicite une seule fois. L'ancien `B_pp^H` ne figure pas dans ce ledger. Le paiement acquis de `I_alpha` figure une seule fois, sous ses prémisses ; aucun `I_a9` n'est payé par substitution. Le terme couvert `2 max(e,0)` reste présent. Les frais des routes H et a9 ne sont pas additionnés.

`B_prime^a9` porte les deux vrais fronts a9 et le coefficient additif Mangoldt sur `N-m` premier. Il ne s'identifie pas à W13 au couple H/alpha. J6 donne sa ligne native modulo 3, mais ne l'estime pas. Les préfixes acquis de `mu*chi` ou un BV portant sur Mangoldt seul n'apportent pas le contrôle du coefficient couplé `mu(m)Lambda_N(N-m)`.

## 6. Témoins et limites de la route pondérée

Le banc conserve la puissance propre active `m=658911`, `N-m=9967^2`, et le témoin de variation harmonique `m=1017399`, `N-m=9949^2`. Ajouter `mu(N-m)^2` au raw les effacerait illégitimement. Au second témoin, le physique de bande est nul mais la différence des préfixes harmoniques est non nulle ; l'argument exact extrait `log(9949)` et utilise l'indépendance rationnelle des logarithmes premiers, sans présumer leur indépendance algébrique générale.

`m=2121` distingue ALL-k et `k>=2` : le physique de bande ALL-k est nul, tandis que le retrait de k=1 crée un poste physique compensé dans le modèle. Ces deux retraits doivent rester joints. `m=112211` devient nul dans le bracket complet réécrit car `mu(m)=0` ; cela ne justifie pas la suppression d'anciennes queues découpées par b.

La ligne J6 prend deux signes : `m=32421` contribue `+(1/2)log(99967579)log(10807)`, et `m=9507` contribue `-(1/2)log(99990493)log(3169)`, avec premiers du premier axe et cofacteurs au-delà de a9. Le candidat `m=31209` a Mangoldt nul. Ces témoins excluent une faveur pointwise uniforme ; ils ne réfutent pas une compensation globale éventuelle.

La réécriture pondérée W2 concerne le bracket complet. Le passage vers `w=Lambda_N(N-m)mu(m)^2` est légitime après cette réécriture, en utilisant `mu(m)^3=mu(m)`, et ne masque pas le premier axe. La matrice Gamma garde les poids réels, DD, DM, MD, MM et les diagonales. Le point `m=323` est un véritable terme modèle seul et sa diagonale est positive. Une énergie positive exacte ne fournit pas un petit opérateur ni le signe demandé. Sur tout point physique où `q|k`, la phase native vaut 1 ; aucune compensation de cette phase n'est déduite des caractères seuls.

## 7. Décision de protocole

| Type d'événement | Décision du Juge |
|---|---|
| Raccourcis V1 et primalité de `m=311` | `REJECTED_BEFORE_COMPILATION`, falsifications arithmétiques concrètes |
| V2, transport conjoint et identité d'énergie corrigés | Identités exactes ; statuts finis conservés, sans gain signé prétendu |
| J3 et PP-a9-paid | Paiements analytiques écrits partiels avec seuils explicites |
| J4 | Paiement qualitatif ; seuil BV supplémentaire non évalué |
| Moment signé premier et terme couvert | Obligations quantitatives encore ouvertes |
| Compilation Lean de cette boucle | Non invoquée ; aucun diagnostic fictif ni lemme auxiliaire substitué à l'objectif |

Les acquis du cadre ne sont pas réouverts par cet audit. Le constat porte sur la capacité des nouveaux mécanismes à payer les postes du ledger exact. Aucun mécanisme nouveau certifié par Lean ne contourne ici l'obstacle de parité pour obtenir la cible sur D_N. Le succès reproductible des identités et des paiements partiels est enregistré ; la condition de victoire reste non satisfaite.

Ce rôle a écrit uniquement ses scripts, son manifeste et ses reçus sous `round9/judge`, ainsi que le présent rapport. Aucun rapport d'un autre rôle, aucun artefact antérieur et aucun état Arbor n'a été modifié. Après le rejeu final réussi, aucune compilation ni répétition supplémentaire des bancs n'a été effectuée.
