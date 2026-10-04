# Boucle 10 — formalisation réelle de E3 et audit du paiement singulier

**TERMINÉ. Certificat Lean auxiliaire obtenu, sans victoire sur la parité.** Le nouveau fichier `lean/PrimeCofactorIdentity.lean` compile avec Lean 4.15.0 et le cache mathlib local. Il prouve l'extraction exacte du cofacteur premier dans le véritable physique capé, puis dans son bracket avec le modèle arithmétique complet. Aucun cofacteur carré-libre n'est supposé. Aucun coefficient libre, petite énergie, identité manquante ou gain cible n'est pris comme hypothèse.

Le paiement écrit E6–E10 de la mobilité singulière est mathématiquement valide dans son domaine. Il n'est pas formalisé dans ce fichier. La compensation signée E11/E12, le seuil supplémentaire BV de la bande physique et le pont couvert `2max(e,0)` restent ouverts. La compilation de E3 ne suffit donc pas à la condition de victoire originale.

## 1. Entrées et gate avant compilation

Le rapport 2 final, `agent2_prime_operator.md`, a été lu intégralement et son SHA vérifié : `55b0eddd21732a6d9052f888d6df7114c4041ad41e8e59c33c6568bab261b4fa`. Le `PROBE_BLOCK.md` de la boucle 10 et la clarification source54 de la boucle 9 ont également été lus. L'exposant littéral de (54) demeure `-sqrt(u/60)` ; `-sqrt(u)/60` est son affaiblissement valide explicitement utilisé.

Le rôle 6 a communiqué son gate E3 sauvegardé avant le premier appel Lean. Chaque tentative du builder a ensuite vérifié le SHA du script réel contre le champ interne `script_sha256` du JSON, N=100000000, le statut global `PASS_FINITE_IDENTITIES_ONLY` et `small_cofactor.status=PASS_IDENTITY_ONLY`.

```
paired_cofactor_checks.py bdee7952e47419fef2a0512d8e74a7234bf3da6800e2dc9561b94f9bd34d5ef2
paired_cofactors.json     909df1b5cd38a4ed42cad65ca8930c47930d7ba8afd356148d87f4c7edcf34b2
agent6.md                3453e489eb94df5a187b107173a9081c95471116ae0369de4dd3d0d1cb7ef413
numerical_replay.json     c94340168a6fd0e3e83f688d4817c9f470c6a876d85d931f19259f8a0ed962a8
```

Le rapport 6 final et les empreintes ont été relus après sa clôture. Les cinq cas E3 comprennent c=1,7,21,231,9 avec p et n réellement premiers, modèles complets et fronts stricts. Le cas c=9 vérifie l'annulation du bracket entier malgré `Lambda(9)=log3`. Les extensions c>a, p<=a ou omettant le garde de Möbius ont leurs falsificateurs propres. Ces extensions n'ont pas été compilées comme candidates. Le gate ne valide aucune borne asymptotique ou globale ; le rejeu numérique isolé est celui du rôle 6, pas une nouvelle exécution par ce rôle.

## 2. Contenu arithmétique réellement formalisé

Le namespace est `GoldbachRound10`. `muR` est la fonction de Möbius mathlib à valeurs entières, coercée dans R. La fonction de Mangoldt est `ArithmeticFunction.vonMangoldt`. Le physique défini littéralement est

```
physical a Q m
 = muR(m) * sum_(1<=k<=Q, k|m, a*k<m)
                     muR(k)*log((m:R)/(k:R)).
```

Le cap est `Finset.Icc 1 Q`, le front est strict et les diviseurs sont réels. Sur un diviseur positif, le quotient réel coïncide avec la valeur du quotient entier m/k utilisée comme cofacteur. Le modèle défini littéralement est

```
W_positive a Q N n m
 = sum_(1<=k<=Q, a*k<m, gcd(k,n*N)=1)
          muR(k)*log((m:R)/(k:R))/(Nat.totient(k):R).
```

Il garde les k libres : ils ne sont pas filtrés par k|m, ni réduits aux diviseurs de c. Le bracket est exactement `log(n)*(physical-muR(m)*W_positive)`. Aucun masque mu(n)^2 ou nouvelle coupe courte n'apparaît.

Les preuves portent sur les conditions arithmétiques `p.Prime`, `1<=c`, `c<=a<p` et `c<=Q` :

1. `activeDivisors_prime_cofactor` prouve l'égalité de supports actifs avec `c.divisors`. Si p|k, le front est impossible puisque p<=k et c<=a impliquent pc<=ak. Sinon k est premier à p, donc k|pc implique k|c. Réciproquement, k|c donne k<=c<=Q et ak<pc. La preuve conserve les égalités c=a et le rejet de la face ak=pc.
2. `sum_muR_divisors` utilise l'inversion Möbius–zêta réelle. `sum_muR_log_divisors` utilise la vraie identité mathlib `sum_moebius_mul_log_eq`, dont le signe est **moins** Mangoldt.
3. `complete_cofactor_log_sum` développe log(pc/d)=log p+log c-log d avec ses non-zéros positifs. La somme devient `Lambda(c)+1_(c=1)log p`, car la somme de Möbius vaut delta_(c=1) et delta_(c=1)log c=0.
4. `muR_prime_cofactor` établit mu(pc)=-mu(c) par c<p, donc gcd(p,c)=1, la multiplicativité de Möbius et mu(p)=-1.

Les théorèmes substantiels obtenus sont

```
physical_prime_cofactor:
 P_a(pc) = -mu(c)[Lambda(c)+1_(c=1)log p].

actual_prime_bracket_cofactor:
 b_a(n,pc) = mu(c)log n
              [W_positive(n,pc)-Lambda(c)-1_(c=1)log p].
```

Le second théorème a le véritable `W_positive` dans son énoncé. Le helper algébrique ne prend pas un coefficient arbitraire à sa place. Le théorème `source_prime_bracket_cofactor` instancie le cap **original** Q=(N-1)/alpha, avec les hypothèses du point n+pc=N, n premier unitaire et pc<N-1. Le nouveau front est a ; alpha n'est pas remplacé par a dans Q.

L'identité locale étant vraie pour tout n et N une fois la géométrie du physique satisfaite, ces quatre hypothèses de prime et de point sont redondantes pour la preuve du wrapper source. Lean signale leurs quatre variables inutilisées ; ce sont des avertissements de linter, pas des erreurs. Le résultat ne prétend pas estimer une somme sur ces points ni prouver la partition globale injective en Lean.

Dans l'interprétation source, gcd(m,N)=1 suit de m=N-n et gcd(n,N)=1 ; le masque physique k|m rend alors gcd(k,N)=1 automatique. Le terme k=1 est actif simultanément dans les deux noyaux et vaut mu(m)log m dans les deux, avec gcd(1,nN)=1 et phi(1)=1. Le raccord avec la version k>=2 n'ajoute ainsi aucune charge. Cette dernière lecture source est auditée ici et dans le gate ; elle n'est pas un nouveau théorème source global du fichier.

## 3. Compilation réelle, erreurs et axiomes

`role3_build.py` utilise exclusivement le compilateur installé

```
C:\Users\Utilisateur\.elan\toolchains\leanprover--lean4---v4.15.0\bin\lean.exe
```

et les bibliothèques compilées du cache mathlib dans `q356-canonical-binding-replay/.lake/packages`. Il ne télécharge ni n'installe rien. Il compile seulement `PrimeCofactorIdentity.lean`, vers un nouvel olean sous `round10/role3_build`. Aucun ancien module du projet n'est rejoué.

Les arguments exacts, LEAN_PATH, version du compilateur, hashes, snapshots textuels des sources et logs sont conservés dans `role3_build_receipt.json` et `role3_build/attemptNN*`.

| Tentative | Résultat réel | Diagnostic |
|---|---|---|
| 01 | Lean exit 1 | L'import `Mathlib.NumberTheory.Totient` n'existe pas. Le bon chemin du cache est `Mathlib.Data.Nat.Totient`. L'import superflu Omega a été retiré avant la tentative suivante. |
| 02 | Lean exit 1 | `rw` ne voyait pas l'application sous la lambda issue de `congrArg`. `dsimp only at h` expose cette application, puis l'inversion Möbius–zêta se réécrit. Le builder avait déjà sauvegardé le reçu et le log lorsqu'un affichage console Python en cp1252 a échoué ; sa sortie a été réglée en UTF-8. |
| 03 | Lean exit 0 | Les trois théorèmes imprimés sont certifiés, sans erreur Lean. Les quatre avertissements du wrapper sont décrits ci-dessus. |

L'affichage `sorryAx` dans la **tentative échouée 02** est le placeholder que Lean propage après une preuve en erreur. Il ne certifie rien et n'est pas une balise ajoutée au code. La tentative 03 réparée imprime pour chaque théorème seulement

```
[propext, Classical.choice, Quot.sound]
```

Un contrôle textuel du fichier final ne trouve aucun token `sorry`, `admit` ou déclaration `axiom`. Il n'y a aucune hypothèse de la cible N/(256u ell), de petite énergie ou de compensation manquante. Les erreurs des deux premières tentatives ne sont pas attribuées au mur de la parité.

```
PrimeCofactorIdentity.lean a31895518a60c169a81cdc43201742b4f91efce6d9b032a6a07cc1a8617a4819
PrimeCofactorIdentity.olean 489d17d3ccbe9752fb1d4711edc06ccd4d80712e0682158f42acede5bcac4e5b
role3_build.py             e0c334c42bc04fd1aca7873c0de58f8956210f54f3ebc3206974016051314640
role3_build_receipt.json   721d8ccbb0819b301b66c235f3a048e165e5328a4737656a1b566a32a82f21b2
attempt03.log             e2374db365b5240dcd7309657555d893f55f927c8fca1244c141402635245b89
```

## 4. Audit exact de E6/E7 : masque mobile et signe

Le cadre prend N pair, u=log N, ell=log u. Pour n premier avec gcd(n,N)=1, n>=3 et n ne divise pas N. Le facteur singulier finitement masqué prend une seule nouvelle base première n. Donc

```
S(nN)/S(N)=(n-1)/(n-2)=1+1/(n-2).                 E6
```

Pour n=3, ce ratio est exactement 2. Le dénominateur n-2=1 demeure dans la somme. Le cas non unitaire n=5 pour N=10^8 a ratio 1 ; le cas n=9 ajoute seulement la base 3 et donne ratio 2. Les extensions exclues du gate sont donc bien fausses, tandis que E6 dans son domaine ne l'est pas.

Le noyau source avec log(k/m) a principal -S(nN). Le noyau `W_positive` est son opposé exact pour k,m positifs, et son principal est donc **+S(nN)**. Le rapport 2 final a corrigé cette orientation avant gel. Il définit epsilon=W_positive-S(nN). E11 garde +S(N)C_S, +R_S et +E_S ; E12, qui soustrait mu(m)W_positive au physique, garde au contraire -S(N)sum mu(m)log n, -R_global et -E_global. Les signes sont cohérents.

Sur m>=ceil(N^(3/4)), la vraie longueur est R_a=min(Q,floor((m-1)/a)). Avec a=ceil(N^(7/16)), les marges entières de l'audit 9 donnent R_a>=N^(1/5) pour u>=10^6. Le même K=nN est pair et <=N^3. Le même endpoint log(R_a/m)A_K(R_a) reste présent et a coefficient en module <=u. Ainsi (54), avec son exposant affaibli explicite, donne bien |epsilon|<=G54/u. Le front vide ou court ne reçoit aucun principal automatique. Ce résultat est un input source auditée, pas une conséquence de la nouvelle identité Lean.

## 5. Audit de l'injection et des constantes E8–E10

Sur la zone canonique c<=a<p, la représentation pc est unique. Si un autre premier p'>a distinct de p divisait pc, la primalité et p'!=p imposeraient p'|c, donc p'<=c<=a, contradiction. Le produit fixe ensuite c. Pour m<N, l'application m->N-m est injective ; le petit n=3 n'est pas exclu de cet argument. Le complément R de la zone reste une vraie sous-somme non estimée, contenant notamment m=1 et les cofacteurs trop grands.

Cette injection justifie un coefficient sigma_n de module <=1 sur des n **distincts**. L'extension comptant aussi la représentation (7,3167) du point 3167*7 doublerait un même n et n'a pas ce contrat. Pour l'ensemble global de n, la distinction est native ; aucun facteur additionnel du nombre de p ne peut être introduit.

Le majorant positif, pour n>=3 et n<N, est exactement

```
|S(N)sum_n sigma_n log n/(n-2)|
 <= S(N)*u*sum_(j=1..N-2)1/j
 <= S(N)*u*(1+u).                                  E8
```

Il inclut j=1. Le facteur singulier du cadre satisfait S(N)<=N/phi(N). Cette comparaison peut aussi se lire directement : S(N)/(N/phi(N)) est le produit des facteurs `(1-1/(l-1)^2)` pour les premiers impairs l ne divisant pas N, obtenu après cancellation des facteurs du produit C2. Ils sont positifs et <=1. Il n'est pas nécessaire d'évaluer C2 numériquement.

L'identité N/phi(N)=sum_(d|N)mu(d)^2/phi(d), puis l'inclusion des diviseurs positifs dans 1..N, donne la borne effective. Le produit positif

```
sum_(d>=1)mu(d)^2/[d phi(d)]
 = prod_l(1+1/[l(l-1)]) <= e <3
```

et la somme harmonique <=1+log N impliquent sum_(d<=N)1/phi(d)<=3(1+u). La somme sur l est <=sum_(j>=2)1/[j(j-1)]=1 ; les produits finis puis la monotonie suffisent. Les constantes ne requièrent ni PNT ni BV. On obtient

```
|R_sing|<=3u(1+u)^2.                               E9
```

Normaliser par N/(u ell) donne 3u^2(1+u)^2 ell exp(-u). À u0=10^24, u0<2^80, 1+u0<2^81 et ell0<2^6 : le facteur positif est <2^330. Comme u0>10000 et e>2, le ratio est <2^(-9670)<10^(-12). Sa dérivée logarithmique par rapport à log u est 2+2u/(1+u)+1/ell-u. Elle est au plus 4+1/log u-u, négative dès u0 et pour tout u plus grand. Ainsi

```
|R_sing|<10^(-12)N/(u ell), pour tout u>=10^24.     E10
```

E10 est un paiement écrit indépendant, uniforme même si N a beaucoup de facteurs premiers. N=10^8 est hors de cet onset ; le PASS fini de E6 ne prouve donc pas E10. E10 paie uniquement la mobilité S(nN)-S(N), pas le principal S(N), son moment signé ou le pont e.

## 6. Portée exacte et obligations restantes

E11 conserve ensemble T_semiprime, -G_prime et +S(N)C_S. Le premier terme impose p et N-pc premiers ; le second impose p et N-p premiers. Les c composites carré-libres contribuent encore avec le signe réel mu(c) au modèle. Leur physique nul ne donne aucune faveur uniforme du modèle. BV de Lambda seule et les préfixes acquis de Möbius ne majorent pas cette combinaison signée.

Par l'injection, |E_S|<=NG54 et la mobilité reçoit E10 ; le modèle de la face m<ceil(N^(3/4)) a le majorant positif annoncé. Ses contributions physiques, le complément R et les principaux restent dans leur bracket. Les charges d'une extraction globale E12 couvrent celles de ses sous-secteurs : on n'ajoute ni une seconde mobilité singulière ni un second crédit pour Z_face. Le paiement properpower de boucle 9 est un autre poste du même ledger, payé une fois.

Le ledger authoritative demeure

```
D_N=B_prime^a+B_pp^a+P_band^{>=2}+Z_face^{>=2}
       +I_alpha+2max(e,0).
```

I_alpha est compté une fois, l'onset source reste u>=10^24, et le seuil BV supplémentaire de P_band n'est pas évalué. E3 ne remplace aucune de ces obligations. Une formalisation gagnante future doit établir une majoration unilatérale indépendante du moment E11 avec son complément et ses faces, ou de la compensation globale E12, puis raccorder ces autres coûts au déficit couvert. Prendre cette majoration comme hypothèse ne satisferait pas la condition de victoire.

Le helper de conservation **de la boucle 10**, importé par chemin explicite sans bytecode, confirme 341 artefacts antérieurs inchangés, dont les 34 fichiers de round9, PNG et olean inclus. Registre SHA `39210db5693d97ad22ffe54bfb3e21c238de207b7cb4f73262aae1e0d3a4f9cb`. PDF et ZIP originaux sont également PRESERVED. Aucun ancien banc, builder ou replay Lean n'a été relancé ; aucune mutation Arbor ou d'un autre rôle n'a été réalisée.

Statuts : `COMPILED_AUXILIARY_ARITHMETIC_IDENTITY`, `SINGULAR_MOBILITY_PAYMENT_WRITTEN_VALID`, `TWO_PRIME_SIGNED_COMPENSATION_OPEN`, `PHYSICAL_BAND_ONSET_UNEVALUATED`, `COVERED_BRIDGE_OPEN`, `VICTORY_FALSE`. Le Juge indépendant peut désormais compiler le fichier final et contrôler le contrat ; ce rapport ne lui substitue pas un verdict.
