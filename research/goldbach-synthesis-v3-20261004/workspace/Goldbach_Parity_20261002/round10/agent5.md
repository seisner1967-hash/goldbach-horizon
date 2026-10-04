# Agent 5 — Juge indépendant, boucle 10

**TERMINÉ — `PARTIAL_NATIVE_COFACTOR_IDENTITIES_WITH_OPEN_SIGNED_COMPENSATION`.** Le rejeu numérique exact et la reconstruction neuve des deux modules réussissent. Le Juge valide 25 nouvelles conclusions auxiliaires distinctes : huit dans `PrimeCofactorIdentity` et dix-sept dans `ShortDivisorComplement`. Le cumul passe de neuf modules et 116 conclusions à **onze modules et 141 conclusions auxiliaires**. Toutes les déclarations nouvelles ont été contrôlées par `#print axioms`, avec uniquement `propext`, `Classical.choice` et `Quot.sound`, ou un sous-ensemble. Aucune preuve incomplète ni aucun nouvel axiome analytique n'est utilisé.

**Victoire : fausse. Score sémantique : 0.** Les identités et les réductions écrites sont utiles, mais aucune estimation indépendante de la compensation signée restante ne ferme le ledger fixé. La portée de la compilation ne doit pas être transformée en preuve de la cible sur D_N.

## 1. Entrées finales, conservation et reproduction

Les cinq rapports, le PROBE, les deux modules finaux et les producteurs numériques ont été lus. Le gel final a attendu les deux signaux explicites TERMINÉ et leurs SHA : rôle 3, rapport `f3bbd0ab002fa7f1a5b1accab55605ee767cec9e5b87c3d8021921ad9d6f0895`, module `a31895518a60c169a81cdc43201742b4f91efce6d9b032a6a07cc1a8617a4819` ; rôle 4, rapport `bc74baa07c966dbf6efe3d25d50d361c6da75a3709e8e6b80532a3bac32eaefc`, module `25f38fcb6f84b73551bf9d4131745d5c234a3187dd3e92a8402f8e81b721b447`.

Le manifeste `judge/input_sha256.json` lie 41 fichiers de production finaux, dont les cinq rapports, les sources, les JSON, les helpers et les logs/snapshots des formalistes. Son SHA est `7813c6e9dddc4a00430dfa9036000a487bb63953e1668d9ec73ad71e4645674d`. Les anciens oleans des producteurs y sont des objets de traçabilité ; ils ne sont pas employés dans la reconstruction du Juge.

Commande complète exécutée avec code de sortie 0 :

```powershell
& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round10\judge\audit-judge.ps1' -Python 'C:\Users\Utilisateur\.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
```

`judge/verify-frozen.ps1` vérifie les 341 fichiers antérieurs avant et après. Il utilise explicitement `round10/conservation.py`, dont l'exclusion des futurs roundNN repose sur leur numéro parsé ; les ajouts aux anciennes boucles sont contrôlés. Le registre conserve le SHA `39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb`, avec les 34 fichiers de round9, ses pixels, ses oleans et le controller9 `ef316624b2c49ee3689de9ce24cbf9ecb531fc05e913760341118c47afc334d3`.

Les sources originales sont également conservées : PDF `bbcbe5849e2b169f01a2d64457ccf7d1f3b25edcf2b5ca911bcf01343586eb24` et ZIP `32b12b8d6823ed71323bb76ed1ba1ed7bc2d1ffad38fa973f043f4ae933e49cd`. Les pixels source54 déjà reproduits en round9 sont protégés ; aucun nouveau rendu inutile n'a été effectué. L'exposant littéral reste `-sqrt(u/60)` et le majorant `-sqrt(u)/60` est son affaiblissement valide. L'onset adaptatif source demeure `u>=10^24`.

Les étapes dépendantes s'arrêtent sur un code de sortie non nul. Aucun ancien banc passé ni ancien module Lean n'a été relancé. Les sources et rapports gelés n'ont pas été modifiés ; aucun état Arbor n'a été écrit par ce rôle.

## 2. Rejeu numérique indépendant, sans exclusion de champs

Seuls les deux nouveaux producteurs `witness_search.py` et `paired_cofactor_checks.py` sont rejoués, avec sorties isolées sous `judge/numerical`. Les mêmes bibliothèques historiques sont importées par chemin vérifié sans écriture de bytecode ; leurs anciens bancs ne sont pas exécutés.

| Sortie | Statut conservé | Résultat du rejeu |
|---|---|---|
| `witnesses.json` | `VERIFIED_FINITE_WITNESSES_ONLY` | Tous champs et tous octets identiques ; SHA `527df6b3bc8a71cdbf6e76b428b048d13c8cf6af764f94d0fb7b94a5f008d598` |
| `paired_cofactors.json` | `PASS_FINITE_IDENTITIES_ONLY` | Tous champs et tous octets identiques ; SHA `909df1b5cd38a4ed42cad65ca8930c47930d7ba8afd356148d87f4c7edcf34b2` |

Les trois contrats `dual_and_matched`, `small_cofactor` et `singular` gardent chacun `PASS_IDENTITY_ONLY`. Le nouveau script reste au SHA `bdee7952e47419fef2a0512d8e74a7234bf3da6800e2dc9561b94f9bd34d5ef2`. Les onze cas appariés ont un premier axe réellement premier et unitaire, avec `N=100000000`, `a9=3163`, `Q=999999` et les deux fronts stricts inchangés.

Tous les certificats W et C sont relus en rationnels : chaque signe positif a une borne inférieure strictement positive, chaque signe négatif une borne supérieure strictement négative, et chaque zéro un polynôme exactement nul. Aucun `UNRESOLVED` n'est admis. Le calcul des logarithmes par artanh réduit les arguments à [1,2], majore positivement la queue géométrique et arrondit vers l'extérieur ; aucun arrondi flottant ne décide les signes.

Le banc conserve `asymptotic_signs_validated=false`, `analytical_payments_tested=false`, `properpowers_removed_from_raw=false`, `global_D_N_estimated=false`, `victory=false` et `Lean_called=false`. La mention `Lean_called=false` appartient au producteur numérique ; le Juge a ensuite invoqué Lean pour les nouveaux modules, donc son reçu général porte `lean_invoked=true`.

Les huit falsificateurs restent séparés :

| Extension rejetée | Témoin et défaut | Statut |
|---|---|---|
| Tout J2 serait favorable | `m=30108669=3*3167*3169`, `n=69891331` premier : `C=log3-W_kernel>0` | `ERROR_FALSIFIER` |
| E3 étendue à `c>a` | `m=3167*3169`, `c=3167>3163` : T vaut zéro, pas `log3167` | `ERROR_FALSIFIER` |
| E3 étendue à `p<=a` | `p=3`, `c=23`, `m=69` : T vaut zéro, pas `log23` | `ERROR_FALSIFIER` |
| Garde de Möbius entier supprimé | `c=9`, `p=3181` : T nu vaut `log3`, mais le bracket entier vaut zéro | `ERROR_FALSIFIER` |
| Fibre courte complétée sans domaine | `c=3183=3*1061`, `p=3307` : U court vaut `-log3183`, pas `-Lambda(c)=0` | `ERROR_FALSIFIER` |
| Ratio singulier étendu au non-unitaire | `n=5` : ratio 1, pas 4/3 | `ERROR_FALSIFIER` |
| Ratio singulier étendu à une puissance propre | `n=9` : ratio 2, pas 8/7 | `ERROR_FALSIFIER` |
| Représentations non canoniques comptées deux fois | `m=22169` : seule `(3167,7)` satisfait `c<=a<p`; `(7,3167)` doublerait le même n | `ERROR_FALSIFIER` |

La recherche vide de `m=p^2` rough est classée `STRUCTURAL_WITNESS_EXCLUSION` : pour ce N, `N mod3=1`, et `p!=3` impose `N-p^2` divisible par 3, donc non premier au-dessus de Q. Ce diagnostic de domaine n'est ni une identité fausse ni une erreur Lean.

## 3. Reconstruction neuve et portée de chaque module

Le compilateur est Lean 4.15.0, commit `11651562caae`. Le cache mathlib exact est celui de `q356-canonical-binding-replay/.lake/packages`, avec les huit chemins de bibliothèques conservés dans le reçu. Aucune installation ni construction des bibliothèques ou anciens modules n'est lancée.

Le dossier neuf de ce rejeu est `judge/fresh_ceb9kae4`. Chaque source finale y est copiée et instrumentée par des commandes `#print axioms` pour **toutes** ses déclarations `theorem`, y compris ses helpers. Les originaux sont conservés octet pour octet en snapshots. Les nouveaux oleans sont absents avant compilation ; aucun ancien olean personnalisé n'est réutilisé. Le scan des parties exécutables exclut `sorry`, `admit`, `axiom` et `native_decide`. Les sorties de chaque axiome imprimé sont contrôlées, et `sorryAx` est absent des sorties réussies.

| Module nouveau | Déclarations contrôlées | Exit Lean | Diagnostics finaux |
|---|---:|---:|---|
| `PrimeCofactorIdentity` | 8 | 0 | Quatre avertissements de variables source redondantes |
| `ShortDivisorComplement` | 17 | 0 | Aucun avertissement ni erreur |

Les deux namespaces distincts conservent 25 noms complets distincts. Les trois ou quatre commandes `#print axioms` des producteurs ne limitaient pas le nombre de déclarations ; le Juge a audité chaque théorème.

`PrimeCofactorIdentity` définit le physique avec `Finset.Icc 1 Q`, `k|m`, `a*k<m`, le vrai Möbius et le logarithme positif `log(m/k)`. Son modèle `W_positive` garde les k libres, le totient, `gcd(k,nN)=1`, le même cap et le même front. Le support actif dans `m=p*c` est prouvé égal à tous les diviseurs de c lorsque `p` est premier et `1<=c<=a<p`, `c<=Q`. L'identité complète de Möbius et Mangoldt conserve le terme `c=1`. La multiplicativité réelle donne `mu(pc)=-mu(c)` sans hypothèse que c soit carré-libre.

Le résultat local compilé est exactement

```text
physical(a,Q,pc) = -mu(c)[Lambda(c)+1_(c=1)log p],
primeBracket = mu(c)log n[W_positive-Lambda(c)-1_(c=1)log p].
```

Le wrapper source garde le cap `(N-1)/alpha`. Les hypothèses de primalité/unité de n, de point `n+pc=N` et de borne `pc<N-1` sont redondantes pour cette identité locale, qui vaut pour tout n,N. Les quatre avertissements `unused variable` sont conservés explicitement ; ils ne sont pas des preuves en erreur. Le module ne certifie pas le reindexage injectif global de la zone S ni sa compensation signée.

`ShortDivisorComplement` conserve le noyau source avec `log(k/m)`. Il prouve le front strict par le quotient entier, la bijection exacte des diviseurs complémentaires et la multiplicativité sur le support carré-libre. Le cap `m<a*(Q+1)` est prouvé à partir du **Q original** dès `alpha>0`, `alpha<=a`, `m<N`. Le cas non carré-libre annule le coefficient entier d'origine ; il ne prétend pas annuler U court. Le point `m=1` est certifié séparément.

Le résultat U1 compilé est

```text
-mu(m)D_a(m) = mu(m)^2[-Lambda(m)-U_a(m)].
```

Le raccord d'unités est également compilé : lorsque `m+n=N` et `n.Coprime N`, tout `k|m` satisfait `k.Coprime(n*N)`. Le masque est retiré sur cette seule fibre prouvée ; aucun masque libre du modèle n'est retiré. Le théorème physique final conserve ce masque, m non nul, n positif, alpha positif et alpha<=a. La primalité de n n'est pas nécessaire à cette identité et demeure requise dans les sommes analytiques du premier axe.

Aucun de ces modules ne prend la cible, une petite énergie, U7 ou une estimation analytique manquante comme hypothèse. Les fonctions arithmétiques sont celles de mathlib et les supports sont littéraux. Les modules restent des certificats locaux auxiliaires : ils ne formalisent ni le budget complet de D_N ni le nouvel argument analytique de signe.

## 4. Échecs techniques réels et falsifications mathématiques

Les logs des producteurs sont figés et conservés sans réexécuter leurs tentatives en erreur. Le rejeu final du Juge a deux codes de sortie 0 et n'a produit aucune erreur nouvelle.

| Production | Diagnostic conservé | Classification |
|---|---|---|
| Rôle 3, tentative 01 | Import `Mathlib.NumberTheory.Totient` absent ; corrigé vers `Mathlib.Data.Nat.Totient` | Technique |
| Rôle 3, tentative 02 | Réécriture sous lambda non exposée ; correction par `dsimp only`. Défaut d'affichage console cp1252 enregistré séparément | Technique |
| Rôle 4, tentative 01 | Réécriture globale de m modifiant aussi m/k ; correction par un calcul localisé | Technique |
| Rôle 4, tentative 03 | `simp made no progress` sur le raccord de masque ; introduction explicite de l'unité et séparation des conditions | Technique |
| Extensions du tableau numérique | Identités réellement fausses sur leurs supports étendus | Falsifications arithmétiques avant compilation |

Les mentions `sorryAx` dans les seules sorties des tentatives échouées sont des placeholders introduits après erreur par Lean. Elles ne certifient aucun candidat et ne sont pas présentes dans les sources finales ou les sorties réussies. Ces défauts ne sont pas attribués au mur de la parité. Le blocage mathématique est précisément l'absence d'une estimation de la combinaison signée restante, après les identités corrigées.

## 5. Audit écrit des signes rough et des charges nouvelles

Sur le support carré-libre et avec `a=ceil(N^(7/16))`, `a^3>N` prouve la partition `j=0,1,2` selon les facteurs premiers >a. Dans J2, `m=c*p*q`, `a<p<q`, le cœur satisfait `c<N/a^2<=N^(1/8)<a` ; tous ses diviseurs sont alors présents. Ainsi U2 donne `C=Lambda(c)+mu(c)W_kernel`. Ce domaine de complétude ne s'étend pas à J1,c>a, ni aux fibres générales coupées. Le point `c=1`, les c composites carré-libres des deux signes et les zéros non carré-libres restent séparés.

Sur le bulk `m>=ceil(N^(3/4))`, `n=N-m>Q` premier, le masque harmonique devient exactement celui de N : n ne divise aucun k<=Q. Avec le préfixe entier `min(Q,floor((m-1)/a))>=N^(1/5)` et l'endpoint source, (54) donne `W_kernel=-S(N)+delta`, `|delta|<=epsilon_W`. Les inputs et inégalités élémentaires écrites justifient `1<=S(N)<10 sqrt(u)`, puis `epsilon_W<=1/4` au seuil source.

U6 est donc un véritable signe unilatéral écrit sur ce bulk : pour m premier rough, `C<=-u/2` ; pour m semipremier rough carré-libre, `C<=-3/4`. Les classes vides contribuent zéro. Les comptes favorables ne sont ni minorés par hypothèse ni extrapolés depuis les deux témoins finis. Le banc à N=10^8 certifie seulement les signes de ses points ; il se situe hors de l'onset u>=10^24.

Le coût de coins U est `E_corner=30 N^(3/4)u^3`, avec l'union `n<=Q` ou `m<M` comptée une fois. La borne directe par point garde les fronts vides, le noyau harmonique entier et le physique. Elle paie `E_corner<N/(1024u log u)` dès `u>=65536`, et moins de `10^(-12)N/(u log u)` au seuil source. Le coût d'extraction R2 est au plus `NG54` et possède la petite marge écrite au seuil source. Ces paiements sont analytiques écrits, sans nouvelle certification Lean et hors validation numérique.

La réduction U7 garde les masses favorables et donne

```text
B_prime^a <= B_J0+B_J1,c>1+H2-S(N)M2
              -(u/2)Theta_prime-(3/4)Theta_2
              +E_corner+N*G54.
```

Les couples p<q et le cœur c sont canoniques : aucun facteur de multiplicité n'est ajouté. `J_c` compte réellement p, q et `N-c*p*q` premiers avec unités, fronts et bulk. H2 est positif sur les c premiers ; M2 conserve les vrais signes de Möbius. La brièveté c<N^(1/8) ne transforme pas cette somme pondérée par trois conditions premières en un préfixe Mertens ordinaire. U7 est un progrès unilatéral partiel, sans estimation de `B_J0+B_J1,c>1+H2-S(N)M2`.

## 6. Mobilité singulière et conventions physiques conservées

Le noyau `W_positive` du rôle 2 est exactement `-W_kernel`, donc son principal est **+S(nN)**. Le rapport final a corrigé son signe avant gel ; E11 et E12 gardent les orientations correspondantes. Sur n premier unitaire, `S(nN)/S(N)=1+1/(n-2)` est une identité de facteurs finis. Le petit n=3 reste présent.

La correction singulière est payée positivement sur des n distincts, avec l'injection canonique `c<=a<p`. Elle est au plus `S(N)u(1+u)<=3u(1+u)^2`, puis inférieure à `10^(-12)N/(u log u)` pour tout `u>=10^24`. Ce paiement E9/E10 est écrit et effectif, mais ne paie que la mobilité de S(nN), pas le principal S(N) et son moment signé. Une représentation dupliquée ou un nombre artificiel de p détruirait son contrat.

Le secteur E11 `1<c<=a<p` est déjà dans J1 de la partition U7 ; son c=1 recoupe le bloc premier rough, tandis que J2 est disjoint. On n'additionne pas les deux extractions comme deux secteurs ou deux crédits indépendants. Une extraction globale E12 couvre les corrections de ses sous-secteurs ; on ne paie pas deux fois R_sing ou une erreur de modèle, et aucun second crédit Z_face n'est créé.

Les témoins non carré-libres `c=9` et `m=3*3167^2` gardent un préfixe non pondéré parfois non nul mais un bracket entier nul. Le cas `c=1` conserve le terme `-log p`. Les points J0 et J1 à fibre incomplète restent positifs dans les certificats finis et ne sont pas effacés par le signe rough. Le modèle conserve tous les k unitaires du préfixe, pas seulement les diviseurs physiques. Le retrait k=1 est conjoint et exact, sans nouvelle charge. Aucune puissance propre du premier axe n'est supprimée du raw.

Sur le nouveau point physique `m=30108669`, q=k=3 et `n mod3=N mod3=1` donnent la phase native 1. Ni cette phase, ni une identité de Gram, ni le seul BV de Mangoldt ne contrôle les poids couplés des moments E11/E12 ou J_c. Les falsificateurs pointwise n'impliquent aucune impossibilité globale des méthodes de poids ou de caractères.

## 7. Verdict par rapport au ledger fixé

Le seul ledger retenu demeure

```text
D_N = B_prime^a + B_pp^a + P_band^{>=2}+Z_face^{>=2}
        + I_alpha + 2 max(e,0).
```

I_alpha est payé une fois avec ses prémisses. Le paiement direct des puissances propres et celui de la face harmonique de round9 restent chacun comptés une fois ; la route H n'est pas ajoutée à la route a. Les nouvelles allowances de coins et de mobilité singulière paient leurs propres erreurs d'extraction, sans remplacer les obligations précédentes.

Restent ouverts : la compensation signée `H2-S(N)M2` avec J0/J1 et les contributions favorables, ou une estimation indépendante de la combinaison E11/E12 avec son complément ; le seuil BV effectif supplémentaire de la bande physique ; et le terme couvert `2 max(e,0)`. Aucune nouvelle hypothèse de petitesse sur ces postes n'est introduite pour produire un théorème compilable.

La compilation des identités auxiliaires et les paiements écrits partiels sont validés dans leurs portées exactes. La condition de victoire sur le résidu D_N n'est pas remplie. **Score : 0. Victoire : fausse.** Le reçu définitif est `judge/judge_receipt.json`. Après ce rejeu final réussi, aucun banc ni module n'a été relancé. Les sources, autres rapports et artefacts antérieurs restent gelés.
