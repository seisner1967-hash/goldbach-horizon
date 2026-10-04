# Agent 1 — deux candidats exacts et leur obligation analytique

Documents lus : monographie (notamment sections 5–6, 9–10 et appendice A), continuation du 1 octobre 2026 et `sources/exact_checks.py`. Les acquis et les profils de coupure sont conservés. La condition de victoire ne peut pas être accordée à une identité finie dont la conséquence quantitative reste une hypothèse.

## Domaine commun et frontière littérale

Posons `alpha = ceil(N^(1/4))`. Pour `1 < m < N`, si tous les premiers divisant **m** sont strictement supérieurs à `alpha`, alors m a au plus trois facteurs premiers, avec multiplicité : quatre facteurs donneraient `m >= (alpha+1)^4 > N`. Sur le support carré-libre, il y a donc exactement un, deux ou trois premiers distincts.

La condition `r > alpha`, dans `m=r*k`, ne suffit PAS à ce domaine : r peut être composite et k peut posséder un petit facteur. Le passage ci-dessous est applicable seulement au sous-secteur où m complet est alpha-rugueux. Le complément et les unités doivent garder leurs sélecteurs originaux. Il ne faut pas mélanger ce profil quart avec le profil huitième.

## Candidat A — correction hypergraphe du projecteur impair

Définissons

`Podd(m) = (mu(m)^2 - mu(m))/2`,

`T3_alpha(m) = #{(p,q,r) : alpha<p<q<r, p,q,r premiers, p*q*r=m}`.

Sur le domaine commun, l'identité exacte est

`mu(m)^2 * Lambda(m) = log(m) * (Podd(m) - T3_alpha(m))`.

En effet : sur un premier, les coefficients sont `(1,0)` ; sur deux premiers ils sont `(0,0)` ; sur trois premiers ils sont `(1,1)`. Pour tout entier non carré-libre, les deux membres sont nuls si l'identité est prolongée avec un facteur `mu(m)^2` devant le projecteur et devant le compteur de triples distincts. Le cas `m=1` peut être traité séparément par `log 1=0`.

La version ordonnée utilise six fois T3 : compter les triples ordonnés de premiers distincts et diviser par 6. La version orientée permet une forme bilinéaire exacte. Si d=p*q avec alpha<p<q premiers, les triples sont `d*r`, avec `r>q`; on a `d<N^(2/3)`. Les restrictions `r>q` et `d*r<N` doivent rester littérales.

Pour un poids réel c(n,m) contenant TOUS les anciens sélecteurs, poser

`A = sum_{n+m=N} c(n,m) Lambda(n) log(m) Podd(m)`,

`T = sum_{alpha<p<q<r, p*q*r<N} c(N-p*q*r,p*q*r) Lambda(N-p*q*r) log(p*q*r)`.

Alors le compte de paires de premiers restreint au secteur rugueux est exactement `A-T`. Il n'y a aucune hypothèse d'annulation dans cette égalité. Si c est positif, T est positif : on ne peut pas le supprimer dans une minoration.

### Test falsifiable

À `N=10^8`, `alpha=100`, prendre `m=101*103*107=1113121` : `Podd=1`, `Lambda(m)=0`, `T3=1`. Toute version omettant T3 est réfutée immédiatement. Pour chaque entier carré-libre alpha-rugueux m<N, tester les coefficients entiers : `primeIndicator(m) = Podd(m)-T3(m)`. Des logarithmes flottants ne sont pas nécessaires.

### Lemme réellement manquant

Il faut une minoration uniforme, avec les sélecteurs réels, de A moins T, ou une majoration unilatérale du résidu correspondant dans le transfert exact. Le caractère impair détecte aussi les triprimes. Estimer cette correction est une véritable corrélation additive `Lambda(N-d*r)` pondérée par les facteurs premiers de d et r. La compilation du projecteur XOR ou de l'identité ci-dessus ne fournit pas cette minoration.

## Candidat B — poids quadratique de Chen à multiplicité bornée

Sur le même domaine carré-libre rugueux, soit `omega(m)` le nombre de premiers distincts divisant m et définissons le poids explicite

`W(m) = 3 - 2*omega(m) + choose(omega(m),2)`.

Ses réponses sont `W(1 facteur)=1`, `W(2 facteurs)=0`, `W(3 facteurs)=0`. Donc

`mu(m)^2 * Lambda(m) = mu(m)^2 * log(m) * W(m)`

pour m>1 dans ce domaine. Le facteur carré-libre conserve les détecteurs originaux. Ce poids est une interpolation quadratique explicite sur la multiplicité bornée; aucune nouveauté analytique n'est revendiquée.

Il possède la forme bilinéaire littérale

`W(m) = 3 - 2*sum_{p prime, p|m} 1 + sum_{p<q primes, p*q|m} 1`.

Le poids est donc un système de poids finis de type Chen, à coefficients 3, -2 et +1, qui élimine simultanément semiprimes et triprimes sur ce domaine. Il ne suppose ni signe favorable de mu ni annulation souhaitée. Dans la convolution additive avec `Lambda(N-m)`, le dernier terme conserve un module d=p*q et un cofacteur k=m/d; le premier et le second restent également dans leur support exact.

### Test falsifiable

Pour chaque m carré-libre alpha-rugueux m<N, calculer exactement omega et vérifier `W=1` si m est premier et `W=0` autrement. Hors de l'hypothèse omega<=3, le poids n'est pas un détecteur : omega=4 donne W=1. Prendre `m=101*103*107*109=121330189` réfute une extension sans borne de multiplicité; ce m est justement hors N=10^8. Les carrés de premiers montrent pourquoi le facteur carré-libre ne peut être retiré.

### Lemme réellement manquant

Pour payer D_N, il faut contrôler le cumul signé des trois incidences (0, 1 et 2 grands diviseurs premiers) dans la convolution avec les premiers de la première variable, avec les faces mobiles. Le produit p*q peut être proche de N, alors que le niveau de distribution classique disponible ne contrôle pas tous ces modules uniformément. Les annulations entre 3, -2*omega et choose(omega,2) sont exactes point par point, mais leur estimation après remplacement par densités est précisément une nouvelle obligation analytique. On n'a pas obtenu le contrôle `D_N <= N/(256 log N log log N)`.

## Contrat terminal conservé

La monographie fournit `D_N = -Sfull + 2*max(e,0)` après le pont couvert exact. Les candidats A et B sont des identités finies seulement. Pour une victoire, la preuve Lean doit en outre relier effectivement l'identité au résidu du support complet et prouver la borne, ou établir un dispositif de contournement dont cette implication est démontrée. Une hypothèse remplaçant directement la corrélation ou sa borne par la cible ne remplit pas ce contrat.

Le contre-exemple d'appariement local `(a,r,y)=(15,77,2)` avec coefficient +4 et aucune masse négative demeure excluant pour toute proposition de simple appariement à racine CRT fixée. Aucun des deux candidats ne prétend réutiliser cet appariement.

## Rapport de communication

Formule A et conditions exactes transmises aux Agents 3 et 6. La formalisation doit distinguer les réponses prime/semiprime/triprime et ne pas appeler le projecteur impair un détecteur de premiers. L'Agent 6 dispose du contre-test triprime ci-dessus et du besoin de vérifier le produit complet m=r*k.
