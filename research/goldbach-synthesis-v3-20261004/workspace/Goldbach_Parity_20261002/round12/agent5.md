# Boucle 12 — audit indépendant des rejets avant Lean

**Verdict : aucun candidat quantitatif admissible, aucune victoire.** Les identités gardées de suppression et du détecteur sont exactes sur les nouveaux contrats contrôlés. Les raccourcis proposés sont réfutés localement ou laissent le moment signé sans estimation indépendante. Aucune compilation auxiliaire n'a été substituée à l'objectif.

`status=REJECTED_BEFORE_LEAN_WITH_VALID_GUARDED_IDENTITIES`, `lean_invoked=false`, `victory=false`, `score=0`. Zéro nouveau module et zéro nouvelle conclusion Lean. Le cumul acquis reste **13 modules et 169 conclusions auxiliaires**.

## Entrées définitives et reproduction

PROBE_BLOCK12, l'observation du coordinateur, les rapports 1, 2 et 6, les six sources et auxiliaires Python neufs, les témoins, gates, manifeste et reçu de rejeu ont été lus. Le gel a eu lieu après le signal `TERMINÉ1`, dernière entrée encore mutable. Les trois empreintes des rapports définitifs concordent :

| Rapport | SHA-256 |
|---|---|
| `agent1_compensation.md` | `896111f4bdc27e79ef352703be83f5b84e2bd26adb5c03644698fe06fcd5775c` |
| `agent2_bilateral.md` | `71e8b1fb2d7a4d20d146e4357ea0a6ab5f7c1fd0af77d1386db50dbaf5ecd91a` |
| `agent6.md` | `ee2383547abc96817911f7120e09246a2d36e579e940004cd8d2062688198759` |

Le manifeste du Juge fige 20 fichiers, dont les trois copies isolées. La commande B_dev exécutée une fois avec succès est :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round12\juge\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

L'audit est en lecture seule pour les entrées de production. Il ne charge ni n'exécute les producteurs ou leurs fonctions arithmétiques. Il contrôle leurs sources, la syntaxe Python, les empreintes, les reçus, toutes les copies isolées, les champs de contrat et les certificats rationnels. Il écrit uniquement son reçu sous `round12/juge`. Une erreur arrête la commande et les étapes dépendantes. Le code final est zéro ; la sortie affiche `Score: 0`.

Le Juge ne relance aucun nouveau banc déjà passé et reproduit, aucun ancien banc, aucun ancien module Lean et aucun rendu PDF. Il ne modifie pas les rapports des autres rôles, les sources, les objets, les archives, le rapport central ou Arbor.

## Conservation et exactitude des reçus

Le registre protège **487 artefacts**, comprenant 405 fichiers antérieurs et les 82 fichiers définitifs de la boucle 11. L'audit recalcule les empreintes de tous les fichiers de ce périmètre et détecte aussi disparitions et additions. Le filtre des futurs répertoires utilise le numéro de `roundNN`, avec exclusion à partir de 12.

La conservation avant et après donne `PRESERVED`, avec les mêmes 487 fichiers. Le contrôleur 11 reste `3860be999898b537fda692534cbf1943225a7aa65e3bb182b48476a5933dd000`. Les originaux PDF et ZIP, les anciens PNG, textes rendus, journaux et objets Lean sont conservés. Le registre a l'empreinte `9a0a1010cdc4ad16eeb28b15f960f1d7dd3621bc91cc4d241a8781ccc2e543b1`.

Les 13 liaisons de `numeric_manifest.json` concordent avec les fichiers. Les imports historiques cités dans les gates concordent avec le registre protégé ; aucun de leurs entrypoints n'est appelé par cet audit. Les trois reçus canoniques et leurs copies de `isolated_output_probe` sont identiques sur **tous les champs JSON et tous les octets**, sans exclusion.

| Sortie | Statut conservé |
|---|---|
| `witnesses.json` | `VERIFIED_NEW_ARITHMETIC_WITNESSES_ONLY` |
| `deletion.json` | `PASS_NEW_NORMALIZED_DELETION_IDENTITY_ONLY` |
| `star_detector.json` | `PASS_NEW_STAR_AND_GUARDED_DETECTOR_IDENTITIES_ONLY` |

Le reçu existant de rejeu garde `PASS_NEW_ROUND12_BYTES_AND_FIELDS_REPLAY`, ses trois codes de sortie zéro et ses empreintes. Les sous-statuts du modèle fini des racines et de la capacité entière de l'étoile restent distincts. Leur réussite n'est pas convertie en paiement analytique.

Les dix `ERROR_FALSIFIER` sont présents aux positions attendues. Les treize positions contenant un certificat de signe sont contrôlées par fractions exactes : bornes ordonnées et intervalle strictement positif ou négatif selon le signe déclaré. Certaines positions reprennent le même certificat dans un sous-rapport ; ce compte n'est pas un compte de nouveaux résultats mathématiques. Aucun `UNRESOLVED` n'est accepté. Les flags de paiement, d'estimation globale, d'asymptotique, d'appel Lean et de victoire restent faux.

## Rôle 1 : étoile et détecteur corrigé

Le graphe de suppression conserve les véritables incidences et noyaux. Une suppression de premier p gardant `m/p≥M` impose `p≤(N−2)/M<a` sous la garde `aM>N−2`. Le noyau des facteurs premiers supérieurs à a reste donc invariant dans ce graphe bulk. Cette observation explique la limitation de l'opérateur choisi ; elle ne prouve pas une impossibilité générale de transport entre fibres par un autre opérateur.

À `N=100000000`, `alpha=100`, `a=3163`, `Q=999999`, `M=1000000`, l'étoile `t=3167·3169` a le cap 9 et l'ensemble complet `{1,3,7}`. Ses trois compléments sont premiers et unitaires. Toute suppression restant bulk revient dans ce cut ; les enfants sortant du bulk restent consignés, avec leurs facteurs et poids. Ils ne reçoivent aucun paiement gratuit.

Le principal entier de cette étoile est

\[
\log3\log n_3+\log7\log n_7
+S(N)(\log n_3+\log n_7-\log n_1).
\]

Sa constante et son coefficient de S sont strictement positifs. Le bracket réel avec ses trois noyaux W est lui aussi strictement positif dans le reçu fini. Le raccord conserve les fronts stricts, les unités et les deux points `k=1`, qui s'annulent ensemble dans D−W. Ce cut est déficitaire pour la capacité locale proposée. Le paiement P5 du modèle commun ne paie pas l'entropie ni la face terminale de l'étoile.

Le second mécanisme garde, pour `m>1`, les expressions

\[
E(m)=\mu(m)+\mu(m)^2\frac{\Lambda(m)}{\log m},\qquad
V(m)=-\frac1{\log m}\sum_{\substack{d\mid m\\d>1}}\mu(d)\Lambda(m/d),
\]
\[
P(m)=(1-\mu(m)^2)\frac{\Lambda(m)}{\log m},\qquad E=V-P.
\]

L'unité `m=1` est séparée. E annule les premiers et les puissances propres du second axe ; il vaut encore μ sur les composites squarefree. Les deux nouveaux J1 ont E égal à −1 et +1, avec un complément réellement premier et une fibre courte incomplète. La positivité ponctuelle n'est donc pas obtenue.

Sur chaque composite squarefree, la couverture absolue complète vaut

\[
\sum_{p\mid m}\frac{\log p}{\log m}=1.
\]

Le facteur `1/log m` n'apporte pas l'économie absolue annoncée après couverture. Sur `m=17³`, le premier complément est actif et `V=P=1/3`, `E=0` : supprimer la correction P serait faux. Cette correction du second axe ne supprime pas les puissances propres du premier axe et ne crée aucun second crédit dans le registre.

Le raccord bilatéral garde `R_tilt`, les masses composites paires et impaires, l'endpoint `SΛ_N(N−1)` et la référence `−S(N)N`. Le renouvellement contient toujours `μ(d)Λ(k)Λ_N(N−dk)/log(dk)`. La majoration absolue ou une borne ordinaire de Mertens ne fournit pas l'estimation de cette combinaison couplée. Le gain indépendant nécessaire reste absent.

## Rôle 2 : suppression première normalisée et modèle complet

L'identité gardée

\[
\mu(m)\log m=-\mu(m)^2\sum_{p\mid m}\mu(m/p)\log p
\]

est exacte, avec le cas `m=1` séparé. Le changement de variables `m=pc` conserve c squarefree, `p∤c`, les unités, `pc≤N−2` et les poids `log p/log(pc)`. Il transfère le vrai détecteur sur `μ(c)Λ_N(N−pc)`, avec les mêmes selections des deux côtés. Il ne rend pas cette incidence indépendante de c.

Sur le secteur premier/premier, les racines de `x(N−cx)` donnent le modèle singulier `S(cN)` sous `gcd(c,N)=1`. Le test fini vérifie les facteurs locaux ; il n'évalue ni produit infini ni densité première. L'omission du garde est réfutée à `c=l=5`, où cinq classes sont racines et non une.

La dispersion proposée garde les quatre termes physique–physique, physique–modèle, modèle–physique et modèle–modèle. Dans sa branche première, elle conserve les trois formes `p`, `N−cp`, `N−c'p`, les collisions parmi les premiers divisant `Ncc'(c−c')`, le diagonal, les masques et le coût CRT `+1`. Les branches raw à puissances propres restent dans les poids réels. Aucune estimation centrée de ce moment, ni du modèle signé en `S(cN)`, n'est dérivée de BV ordinaire.

Le secteur `c=1` reste `R_N^(Λ)−S L_N^(Λ)`, la référence reste `−S(N)N`, et le complément `c>a` est conservé. Le nouveau premier axe `n=8017²` a `Λ_N(n)=log8017` et `theta_N(n)=0` ; tous ses cofacteurs transférés sont longs. Ajouter `μ(n)²` ou les supprimer changerait le problème.

Le polynôme de la seule sélection `{29,561}` vaut `Az+Bz³` avec A,B positifs. Son défaut de log-concavité est `−AB<0`. Cela réfute la promotion sur **toute sélection physique**. Le polynôme global et une éventuelle propriété globale différente restent ouverts.

## Qualification des dix rejets

| Position testée | Ce qui est rejeté |
|---|---|
| Étoile entière | Capacité complète favorable dans ce cut bulk |
| Deux J1 squarefree | Économie absolue `L1≤1/log m`, deux témoins |
| `m=17³` | Omission de la correction properpower du second axe |
| `m=1251` | Suppression du coefficient entier `μ(m)²` |
| `m=561` | Omission du dénominateur logarithmique |
| `m=561` | Remplacement de tous les poids normalisés par 1 |
| Premier axe `8017²` | Complétion par les seuls cofacteurs courts |
| `c=l=5` | Suppression de la garde d'unité du modèle |
| Sélection `{29,561}` | Log-concavité héritée sur toute sélection |

Ce sont dix réfutations locales d'assertions précises. La discordance provisoire d'une liaison de témoins, corrigée avant leur gel, était une mise à jour de métadonnée, pas une erreur mathématique, une altération ancienne ou un échec Lean. Aucun message de compilateur, `sorry` nécessaire ou échec Lean fictif n'est enregistré en boucle 12.

## Domaine source et registre encore ouvert

Les témoins finis sont à `N=10^8`, donc hors du domaine source `u=log N≥10^24`. Un contre-exemple à une assertion universelle de poids ne réfute pas un théorème éventuel limité au domaine source. Le déficit principal symbolique de l'étoile, sa réalisation finie et l'invariance structurelle du graphe ont des portées distinctes ; aucune n'est promue en no-go global.

Le seuil adaptatif et (54) restent inchangés : exposant source `−sqrt(u/60)`, majorant plus faible valide `−sqrt(u)/60`, anciens rendus préservés. Les puissances propres raw du premier axe, les quatre signes de Möbius, les unités, conducteurs, fronts, `+1` et la phase native égale à 1 sur `q|k` sont conservés. Aucun annulus acquis n'est utilisé pour effacer le préfixe bas.

Le registre unique est toujours

\[
D_N=B_{\mathrm{prime}}^a+B_{\mathrm{pp}}^a
+P_{\mathrm{bande}}^{\ge2}+Z_{\mathrm{face}}^{\ge2}
+I_\alpha+2\max(e,0).
\]

H2, les célibataires et faces, J0/J1, le moment bilatéral signé et son principal de référence, la calibration BV supplémentaire de la bande physique et `2max(e,0)` restent ouverts dans leurs routes respectives. Les crédits acquis gardent leur compte unique. Aucun gain de compensation globale ne résulte des identités corrigées de cette boucle ; la condition de victoire reste insatisfaite.

## Empreintes définitives

| Artefact | SHA-256 |
|---|---|
| `juge/input_sha256.json` | `4f3e74b62119ca643ae25ec4f00f11a7163c1e9fb4bd129bb84350bfe25a0e6f` |
| `juge/judge_receipt.json` | `f3be32fd176a20aeff5a915eb5d242b22f06823ab0323a7fca5714af54d8ae57` |
| `juge/audit-judge.ps1` | `875581d1126a06a7eb8cf76066642b1f43ca5b68fea9a1440de0a0a96a5955c6` |
| `numeric_manifest.json` | `e6c7321c0584827e72e1850f0053018b598e35229bc818affaf1b83462198592` |
| Rejeu existant `numerical_replay.json` | `653b4089491e6f18050394e226208dcdd287c1e16e97adf64fe0b9f0b082bcc0` |

Le reçu du Juge relie tous les inputs gelés, les trois rapports, les sources et auxiliaires, les statuts distincts, les dix rejets, les certificats stricts, les copies intégrales et la conservation avant/après. Aucun test supplémentaire n'a été lancé après le passage de cet audit.
