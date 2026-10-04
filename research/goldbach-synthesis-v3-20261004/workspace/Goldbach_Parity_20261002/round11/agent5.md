# Boucle 11 — jugement indépendant définitif

**Verdict : résultat partiel, aucune victoire.** Le rejeu numérique est exact et les deux nouveaux modules Lean compilent fraîchement, sans erreur, avertissement ni contournement du noyau. Le paiement écrit de P5 concerne seulement le modèle commun de deux incidences premières. Il ne ferme pas la compensation signée du registre fixé.

`lean_invoked=true`, `victory=false`, `score=0`.

## Gel, reproduction et conservation

Le gel a été réalisé après les deux signaux `TERMINÉ` des formalistes et la clôture des cinq rapports de rôle. Le manifeste contient 51 fichiers de production, les cinq rapports définitifs, les deux nouvelles sources Lean, la dépendance ancienne requise et les entrées numériques finales. Les journaux et objets des producteurs sont conservés comme traces ; leurs objets compilés ne servent pas à la preuve indépendante.

La commande de reproduction, exécutée une seule fois avec succès, est :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round11\judge\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

`audit-judge.ps1` appelle successivement la conservation avant exécution, `run-judge.py`, puis la conservation après exécution. Chaque étape dépendante s'arrête sur un code non nul. Le code final est zéro et la sortie contient `Score: 0`. Le score exprime l'absence du mécanisme de victoire demandé, et non un échec des vérifications locales.

Les 405 artefacts antérieurs, dont les 64 artefacts définitifs de la boucle 10, sont identiques avant et après. Le contrôleur 10, le PDF et le ZIP originaux, les anciens objets Lean, les images et les textes rendus sont préservés. Les exclusions des futurs répertoires `roundNN` utilisent leur numéro analysé ; elles ne sont pas un préfixe ambigu. Aucun ancien banc numérique déjà passé n'a été relancé. Aucun ancien module indépendant n'a été recompilé hors de la dépendance nécessaire. Aucun rendu PDF n'a été refait. Aucune modification d'Arbor n'a été effectuée.

## Vérification numérique indépendante

Les trois nouveaux producteurs ont été exécutés séquentiellement avec `--output-dir`, dans `judge/numerical`. Les sources et leurs auxiliaires ont les empreintes attendues. Les trois objets JSON complets et leurs octets sont identiques à ceux de production, sans exclusion de champ.

| Sortie | Statut conservé | Tous champs et octets identiques |
|---|---|---|
| `witnesses.json` | `VERIFIED_NEW_FINITE_WITNESSES_ONLY` | Oui |
| `ap_prefix.json` | `PASS_NEW_FINITE_CONTRACTS_ONLY` | Oui |
| `paired_axes.json` | `PASS_NEW_PAIR_IDENTITY_ONLY` | Oui |

Les sous-statuts restent également distincts : identité locale finie, produit fini B6 sous ses gardes, développement exact du préfixe sur le même ensemble premier restreint, distinction entre préfixe bas et bande, partition finie complète avec P2. Le contrôle couvre 16 diviseurs dans le produit B6, 12 couples de coupure/profondeur, cinq premiers dans l'ensemble restreint et deux partitions 3-adiques, à `N=100000000`. Il ne couvre pas toute la somme physique ni une estimation asymptotique de `D_N`.

Les 13 statuts `ERROR_FALSIFIER` sont conservés. Ils réfutent les raccourcis testés : suppression des gardes d'unité ou de squarefreeness, remplacement du PPCM par un produit dans les intersections, disparition de la queue, confusion entre préfixe bas et bande, signe ponctuel de G, suppression des puissances propres au premier axe, paire déclarée favorable à partir de son seul modèle, omission des incidences ou de la face terminale. Les 15 certificats de signe utilisent des bornes rationnelles ordonnées et strictes. Aucun certificat `UNRESOLVED` n'est accepté.

Les deux partitions testées ont `X={1,3,7}`, `D={1}`, `3D={3}`, `F={7}`. Leur seule base appariée a Möbius positif : elles ne testent pas le paiement analytique P5 de la branche défavorable. Les drapeaux `analytical_payments_tested`, `global_D_N_estimated` et `victory` restent faux.

## Reconstruction Lean fraîche

Compilateur : Lean 4.15.0, cache mathlib correspondant, huit paquets locaux exacts. Les objets personnalisés sont produits dans le nouveau répertoire `judge/fresh_uyzjbvk0`. Aucun objet du producteur n'est importé. `ThreeAdicPrimePairing` importe `ShortDivisorComplement` : cette source de la boucle 10, d'empreinte `25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447`, est copiée et reconstruite d'abord.

| Module | Théorèmes inspectés | Définitions imprimées supplémentaires | Code de sortie | Avertissements | Compte nouveau |
|---|---:|---:|---:|---:|---:|
| `ShortDivisorComplement` | 17 | 0 | 0 | 0 | 0 : dépendance |
| `SquarefreeLcmCoefficient` | 9 | 0 | 0 | 0 | 9 |
| `ThreeAdicPrimePairing` | 19 | 15 | 0 | 0 | 19 |

Chaque nouveau théorème est compté depuis la source et inspecté par `#print axioms`. Les 15 définitions imprimées du second module sont auditées séparément et ne sont pas ajoutées aux conclusions. Toutes les dépendances constatées appartiennent à `propext`, `Classical.choice`, `Quot.sound` ; certaines déclarations n'en utilisent aucune. Le scanner du code exécutable, après traitement des commentaires et chaînes, ne trouve aucun `sorry`, `admit`, déclaration `axiom` ou `native_decide`. Les journaux indépendants ne contiennent pas `sorryAx`.

**Compte confirmé : 28 nouvelles conclusions auxiliaires ; cumul de 13 modules et 169 conclusions.** Les 17 conclusions de la dépendance ne sont pas recomptées. L'ancien cumul de 11 modules et 141 conclusions reste la base de ce calcul.

## Portée du coefficient au PPCM : B2–B13

Le nouveau théorème B6 est un véritable produit arithmétique fini. Pour P squarefree et r divisant P, il prouve sur les nombres rationnels :

\[
\sum_{d\mid P}\frac{\mu(d)}{\varphi(\operatorname{lcm}(r,d^2))}
=\frac1r\prod_{\substack{p\mid P\\p\nmid r}}
\left(1-\frac1{p(p-1)}\right).
\]

Les théorèmes intermédiaires portent sur le vrai totient, le PGCD, le PPCM et la fonction arithmétique multiplicative normalisée. Les cas `P=1`, `r=1` sont inclus. Le wrapper d'unité conserve le filtre extérieur sur r et le filtre intérieur sur d ; ils sont établis sous `gcd(P,N)=1`. Le support est l'ensemble des diviseurs de P. Ce théorème n'identifie pas ce support avec la coupure `d≤D`, ni avec une série infinie.

L'audit écrit B2–B13 conserve le préfixe entier `r≤a`, son morceau bas, le masque réel d'unités, l'intersection via `lcm(r,d²)`, le terme principal et la queue du développement de `μ²`. En particulier, la tête du développement ne reçoit pas un nouveau masque `μ²` : le témoin `m=3·3217²` a une tête non nulle et une queue compensatrice, tandis que le détecteur complet est nul. Le premier axe reste `Λ_N`, avec ses puissances propres, et le contrôle des progressions porte sur le même ensemble restreint et les mêmes caps.

Les paiements écrits de queues et de référence ne minorent pas le moment bilatéral B13. Le terme principal reconstitue la référence déjà présente. Le témoin `m=483=3·7·23`, avec `N-m` premier, réfute le signe ponctuel proposé pour G ; il ne démontre aucune impossibilité globale. La calibration BV supplémentaire reste non évaluée. Aucun nouveau théorème Lean ne postule ces bornes analytiques ou la cible finale.

## Portée de l'appariement 3-adique : P1–P6

Les 19 théorèmes raccordent le vrai bracket physique local à deux valeurs du noyau harmonique W, avec deux indicatrices de primalité et d'unité. Ils conservent le cap source, le point `k=1`, les fibres incomplètes et le terme entier original. Pour `m=c p q`, les gardes de J2 établissent le filtre court, `μ(c p q)=μ(c)` et `Λ(c p q)=0` ; le cas d'incidence nulle n'est pas remplacé par une valeur principale.

La partition finie exacte `X=D ⊔ 3D ⊔ F` repose sur `3∤N`, avec le masque `gcd(c,Npq)=1`. Le cap `C=floor((N-Q-1)/(pq))` garde le décalage `+1`, et les hypothèses arithmétiques établissent `C≤a` et les points physiques. P1 est une somme finie de brackets réels sur une fibre canonique `p<q`. P2 sépare exactement le principal en entropie, modèle commun, célibataires et faces. Il ne supprime aucun de ces termes. La définition réelle de S utilise ses facteurs premiers ; l'identité P2 ne démontre pas les bornes analytiques de S.

Le raccord de W au principal sous (54), puis le crible des deux premières incidences, restent des preuves écrites. L'audit vérifie les racines du produit `n(3n−2N)`, le masque `3N`, le facteur `S(3N)=2S(N)` et le coût CRT `+1` pour chaque racine. La formule des couches conserve `Q<n_3<n<N`. Le domaine `3∤N` est essentiel à cette extraction ; les autres N gardent le moment initial.

P5 améliore le traitement écrit du **modèle commun seul**. Avec `u=log N`, `ell=log u`, le majorant obtenu est

\[
E_{\mathrm{common}}
=\frac92 C_{\mathrm{sieve}}S(N)^2\frac{N}{u^2}
+2S(N)\sqrt N,
\qquad C_{\mathrm{sieve}}=\frac{134217728}{2541}.
\]

Le raccord `S(N)<3ell` et les estimations monotones à `u≥10^{24}` donnent le paiement écrit inférieur à `10^{-12}N/(u\,ell)`. P5 remplace le paiement central P4, qui n'est pas additionné une seconde fois. La masse commune favorable demeure conservée sans être minorée gratuitement. Ce résultat ne contrôle ni l'entropie H2, ni les célibataires, ni les faces ; il ne transforme pas le bracket réel entier en ce seul modèle.

Les témoins numériques montrent précisément ces distinctions. Deux axes premiers peuvent avoir un modèle commun négatif et un bracket réel positif. Si le premier axe de la paire n'est pas premier, la vraie contribution principale peut être positive alors que le quotient logarithmique sans indicatrices est négatif. Pour `c=7`, la face terminale reste active lorsque le point `3c` sort du domaine physique.

P6 conserve donc H2, les célibataires, les faces, les termes J0/J1, la masse physique première, l'erreur totale de (54) et les coins. Le crédit des cofacteurs premiers ou semipremiers de la route antérieure n'est pas ajouté une deuxième fois. L'erreur de (54) est payée une seule fois sur le J2 entier.

## Échecs techniques et falsifications mathématiques

| Trace | Nature | Conclusion du juge |
|---|---|---|
| Rôle 3, tentative 01 | `nlinarith` sous une lambda ; réparé par exposition avec `dsimp` | Échec technique de preuve, pas un blocage de parité |
| Rôle 3, tentatives 02 et 03 | Compilation réussie ; précision finale du filtre d'unité intérieur | Source finale reproduite sans avertissement |
| Rôle 4, précontrôle | Forme du dictionnaire de partitions incorrectement lue | Erreur du script préparatoire, avant Lean |
| Rôle 4, tentative 01 | Orientation de coprimalité, lemme de multiplication, paramètres et sommes finies | Erreurs techniques locales réparées |
| Rôle 4, tentative 03 | Quotient et soustraction naturels opaques dans le raccord de P1 | Erreurs techniques réparées avec les identités de soustraction |
| Rôle 4, tentatives 02, 04 et 05 | Compilations réussies ; gardes source finales explicites | Source finale reproduite ; 19 théorèmes et 15 définitions audités |
| Les 13 `ERROR_FALSIFIER` | Contrats mathématiques raccourcis faux sur les témoins déclarés | Raccourcis rejetés ; les identités corrigées restent valides |
| Registre signé encore ouvert | Absence d'une estimation suffisante du moment réel complet | Résultat partiel ; aucune erreur de compilateur inventée |

Le `sorryAx` que Lean peut montrer pour une tentative en erreur est une conséquence de cette tentative non acceptée ; il n'apparaît dans aucune preuve finale ou compilation indépendante réussie. Les traces historiques sont conservées, sans fabriquer un échec Lean pour représenter un problème analytique.

## Registre et condition de victoire

La route unique reste

\[
D_N=B_{\mathrm{prime}}^a+B_{\mathrm{pp}}^a
+P_{\mathrm{bande}}^{\ge2}+Z_{\mathrm{face}}^{\ge2}
+I_\alpha+2\max(e,0).
\]

Les paiements déjà acquis ou écrits sont conservés dans leur portée. Le paiement des puissances propres de `B_pp^a` est effectué une seule fois ; il n'est pas ajouté à une autre route signée. La face modèle et les nouveaux paiements écrits communs ne ferment pas `B_prime^a`. H2 et les moments signés de P6/B13, J0/J1, les célibataires et les faces d'appariement, la calibration du seuil BV de la bande physique et `2max(e,0)` restent à contrôler.

Le seuil adaptatif source est bien `u≥10^24`. L'exposant littéral de (54) est `−sqrt(u/60)` ; `−sqrt(u)/60` est le majorant volontairement plus faible déjà rendu et vérifié. Les anciens pixels et leurs reçus sont préservés. Les constantes de budget 1024 n'altèrent pas ce seuil.

La compilation certifie des identités arithmétiques et des partitions raccordées aux définitions réelles. Elle ne certifie pas la compensation quantitative manquante ni la borne `D_N≤N/(256 log N log log N)`. La condition de victoire demeure insatisfaite.

## Empreintes et sorties définitives

| Artefact | SHA-256 |
|---|---|
| `judge/input_sha256.json` | `e16d2ba7a21deb4fc89939fd7fb21b583be5747bf03799b2c32237b417c072c9` |
| `judge/judge_receipt.json` | `951387533f0f3ffe2367cc4572c2a67e1c04583e326a9a384464ab1049ea8aae` |
| `judge/numerical/replay_receipt.json` | `c190f5c0a61b9a3d86fa8d3a5466a02c5c2e6a3b129867dab208530f128679e7` |
| Source finale `SquarefreeLcmCoefficient.lean` | `f791b4be0f731244a44449f27bb236c7890a8265c0e7fa6d55150a1a230e1ba6` |
| Source finale `ThreeAdicPrimePairing.lean` | `b3c22b714566b3d6e1fa864c4414201c9a2215c506350bdf1c8373a598d26f48` |

Le reçu lie les cinq rapports finaux, les sources et auxiliaires numériques, tous les champs des trois gates, les journaux de compilation indépendants, chaque nom de théorème et ses axiomes, les objets neufs, les scripts de reproduction et la conservation avant/après. Le manifeste et les reçus sont définitifs. Aucun test supplémentaire n'a été lancé après ce passage réussi.
