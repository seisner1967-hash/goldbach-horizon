# Boucle 7 — audit du raccord des caractères à la ligne native

Agent 4, 2 octobre 2026. Sources consultées : `agent2_nondegenerate_characters.md`, `jacobi_checks.py`, `jacobi.json`, `trace_checks.py`, `trace.json` et la monographie fournie, §5, texte extrait autour des lignes 640–680. Le rapport de l'idéateur est conservé comme version finale proposée ; aucune source acquise ou boucle antérieure n'est modifiée. Cet audit mathématique n'est pas une certification Lean.

**Verdict : rejet avant formalisation du transfert « petites sommes de Jacobi ⇒ petit résidu HH ».** N1–N9 sont des identités exactes standard dans leurs domaines. Elles reconstruisent la masse physique principale et ses exceptions, sans estimer le signed-root discrepancy d'origine. La ligne native n'a pas le même facteur de caractère ; son secteur divisible constitue un témoin exact du raccord invalide. Aucune nouvelle identité de contournement admissible au Juge Lean n'a été obtenue.

## 1. Insertion physique et modèle indépendant

Omega conserve les vrais tuples `a=u*v*x`, `r=s*t*zeta`, `n=a*b`, `m=r*k=N-n`, leurs quatre signes **mu(u)mu(v)mu(s)mu(t)**, les logarithmes `log(b)*log(r)`, le core, les deux détecteurs prescrits à cette composante HH, le masque unitaire à N, la rugosité du premier côté et chaque front strict. Le profil brut distinct n'est pas enrichi d'un nouveau filtre mu(n)². Le module CRT demeure a*r ; ni le conducteur de signe ni un p auxiliaire ne le remplace.

Pour un premier impair p ne divisant pas N, définir Omega_p par `p∤n*m`, R_p sur son complément **avant de soustraire le modèle**, et

`T_chi = sum_(Omega_p) c(omega)*chi(n)*conj(chi(m))`.

Tous les facteurs de caractères restent présents : chi(b), chi(u), chi(v), chi(x), conj(chi(k)), conj(chi(s)), conj(chi(t)), conj(chi(zeta)). La partition N3 est exacte : `C_HH=R_p+T_chi0` lorsque C_HH est précisément le porteur physique ainsi désigné. Sur Omega_p, n/m est unité modulo p et ne vaut jamais -1, car n+m=N et p∤N. L'orthogonalité donne N4 avec tous les p-2 caractères nonprincipaux :

`C_HH = R_p - sum_(chi!=chi0) conj(chi(-1))*T_chi`.

**Le raccord au résidu conserve séparément le modèle :**

`E_HH = R_p - sum_(chi!=chi0) conj(chi(-1))*T_chi - M_HH`.

Cette égalité exige l'identification exacte de C_HH à Omega et sa normalisation originale. Aucune insertion dans M_HH ne découle d'un tuple physique n+m=N. Les corrections W, autres composantes et défauts de couverture restent dans leur comptabilité d'origine. R_p ne peut contenir silencieusement un modèle centré signé ; sa définition est la partition du porteur physique.

Si p<=W, I_W(n) exclut p|n mais permet encore p|m. Si p>W, les deux exceptions existent. Elles sont disjointes puisque p∤N. Aucun argument ci-dessus ne les borne. Un caractère exclu d'un acquis de nonexceptionnalité est également requis par la résolution complète N4 ; sa contribution ne disparaît pas.

## 2. Raccord natif : les facteurs conj(chi(N)) et conj(chi(m)) diffèrent

Sur le support réel `gcd(n*N,k)=1`, l'orthogonalité native donne exactement

`1_(k|m)-1/phi(k)`
`= sum_(chi mod k,chi!=chi0) chi(n)*conj(chi(N))/phi(k)`.

La constante à conjuguer est N, et non m. Remplacer conj(chi(N)) par conj(chi(m)) change la ligne et son support. En particulier, si un premier p divise k dans DIV, `m=r*k` est divisible par p pour **toute la fibre**, tandis que n=N-m est unité p. Les nouveaux twists modulo p valent zéro, y compris celui du caractère principal prolongé par zéro ; Omega_p est vide et toute cette fibre demeure dans R_p. Le caractère non dégénéré de N6 n'est pas disponible : p divise alors C=k*s*t.

Le banc fournit un tuple original entier à N=100000000 :

`b=101,u=103,v=107,x=43,k=7,s=3,t=71,zeta=34967`,
`n=47864203`, `m=52135797`, `a=473903`, `r=7447971`.

Il conserve y=W=2, les quatre signes -1 (produit +1), les deux produits carrés-libres, les unités à N, le core, k<=999999 et r>100. On a `m=7*r`, `n mod 7=N mod 7=2`. Chaque nouveau produit `chi(n)*conj(chi(m))` modulo 7 est zéro. Chaque facteur natif `chi(n)*conj(chi(N))` vaut 1 ; la ligne centrée vaut **1-1/6=5/6**. Le poids développé de ce tuple est positif `log(101)*log(7447971)`. Ce témoin falsifie un remplacement de la ligne native par le twist de Jacobi ; il ne prouve aucun signe de la somme HH globale.

Si un premier p est pris dans le CRT a*r d'un tuple, il divise a ou r, donc n ou m. La composante qui exige simultanément deux axes p-unitaires élimine ce tuple. Pour tout q>1 divisant a*r, au moins un premier de q rencontre un axe et le produit de caractères modulo q prolongés par zéro s'annule. Cette assertion est par tuple ; un conducteur choisi en fonction du tuple ne devient pas automatiquement un caractère fixe sur une famille entière. Un p auxiliaire copremier à a*r peut encore rencontrer b ou k ; il faut garder ces exceptions pour assurer p∤A*C, avec A=b*u*v et C=k*s*t.

## 3. Trace primitive antérieure : conservée, sans nouvelle oscillation

La monographie §5 donne, pour q carré-libre sur unit-n et unit-N,

`P_q(m) = product_(p|q) ((p-1)*1_(p|m)-1)`.

Quand gcd(q,m)=1, chaque facteur vaut -1, donc `P_q(m)=mu(q)` et

`mu(q)*P_q(m)/phi(q)=1/phi(q)`.

Les deux facteurs affichés ne constituent pas deux oscillateurs indépendants. Cette trace est un acquis explicitement conservé ; la nouvelle insertion ne la remplace pas et ne l'annonce pas comme innovation. Pour q=p premier, `P_p(m)/(p-1)` est exactement la ligne native : `(p-2)/(p-1)` sur p|m et `-1/(p-1)` hors ce secteur, sur les unités n,N. Le nouveau twist efface précisément le premier secteur. Les expressions de trace primitive carrée-libre ne sont pas étendues aux q non carrés-libres ; le diagnostic q=9 du banc ne change pas leur domaine.

## 4. Jacobi complet, phases et reconstruction principale

Dans une fibre fixée A*x+C*zeta=N, le twist complet est

`tau_chi(zeta)=chi(N-C*zeta)*conj(chi(C*zeta))`.

Pour p∤N*C et chi nonprincipal modulo p, la substitution `y=C*zeta/N` montre que `(1-y)/y` parcourt les unités sauf -1, avec deux résidus exclus y=0,1. Par conséquent N6 est exacte :

`sum_(zeta mod p) tau_chi(zeta)=-chi(-1)`.

Omettre conj(chi(C)) multiplie la réponse par chi(C) et donne **-chi(-C)**. Les caractères d'ordre 4 exigent donc la phase complète ; aucune approximation complexe flottante ne la remplace. La moyenne nonprincipale vaut -chi(-1)/p, non zéro. La somme reconstruite par N4 de tous les p-2 modes est

`-sum_(chi!=chi0) conj(chi(-1))*(-chi(-1))=p-2`.

Elle restitue exactement la projection principale, de moyenne `(p-2)/p`. Un module 1 pour chacune des sommes complètes n'est donc pas une réserve de cancellation du principal original. Le cas ancien p|N reste séparé : le twist complet y est constant chi(-1) sur les unités.

Avec `rho_chi=tau_chi+chi(-1)/p`, garder les modes joints avant les valeurs absolues donne N9, y compris aux deux résidus nonunitaires :

`-sum_(chi!=chi0)conj(chi(-1))*rho_chi`
`=1_(p∤(N-C*zeta)*C*zeta)-(p-2)/p`.

Sur une progression de pas unité p, chaque période a somme zéro. Sur un préfixe résiduel de longueur h<p, la somme est `2*h/p` moins le nombre (0,1 ou 2) des classes exclues rencontrées, donc son module est <=2. Par Abel, un poids F paie au plus une constante fois `sup|F|+Var(F)` et le nombre de morceaux. Cette correction du coût des modes séparés retrouve une erreur de plancher standard pour deux classes ; elle n'est pas une estimation de la somme extérieure contre les quatre vrais signes.

Si p divise le pas, le résidu de zeta est fixe : la phase et le membre centré peuvent être constants non nuls. La borne de préfixe <=2 ne s'applique alors pas. Les exceptions de `jacobi.json` sont bien conservées.

## 5. Compatibilité CRT, masques et nombre de points

Le CRT général de la boucle 6 reste correct. Pour `d²|zeta,e²|n,f|zeta,ell|n`, poser

`L=lcm(d²,f)`, `M=lcm(A,e²,ell)`, `g=gcd(C*L,M)`.

Une cellule avec g ne divisant pas N est vide, avant tout inverse. Sinon, avec `M'=M/g`,

`v0=(N/g)*(C*L/g)^(-1) mod M'`,
`zeta=L*(v0+M'*j)`.

Le cas M'=1 prend v0=0. Remplacer L par f*d² exige gcd(d,f)=1 ; remplacer M par A*e²*ell exige les autres coprimalités. e partageant A est conservé. d partageant ell est traité par compatibilité, non supprimé après une fausse inversion.

Pour la composante exacte p-unitaire, p|A ou p|C la rend vide. Les d contenant p sont exclus par zeta unité, les e ou ell contenant p par n unité ; f|rad(C*N) est premier à p dès que p∤C*N. Ces suppressions utilisent les masques exacts avant leur développement, ou le regroupement signé complet après inclusion-exclusion. Elles ne sont pas des zéros de chaque cellule entièrement développée sous valeur absolue. Dans les cellules retenues, p∤L*M, donc p∤L*M' et N6 s'applique à un cycle complet en j. Les fronts restent ceux de la fibre d'origine ; son nombre de points est au plus `1+length(J)/A`, puis `1+length(J)/(L*M')`. Les +1, zeta=1, les queues carrées et les moments divisoriels sont tous présents.

Précision de portée du banc complet : C=10403 est unité aux six premiers testés, mais A=273 est divisible par **3,7,13**. Les sommes N6 calculées à ces p sont de justes diagnostics complets de normalisation **sans le masque A** ; elles ne sont pas des moyennes admissibles de la vraie fibre A=273 p-unitaire, qui est vide. Le banc CRT avec p=11, M=819 est admissible : il conserve les douze cellules e=3 et leurs twists 0,+1,-1. Ces cellules de l'expansion signée ne sont pas douze tuples HH carrés-libres.

## 6. Limites numériques, coût et gate Lean

Le code Jacobi utilise tous les caractères nonprincipaux pour p=3,7,11,13,17,19, des polynômes de phases réduits par les polynômes cyclotomiques exacts, une centration rationnelle, 44944 préfixes et cinq tuples HH admissibles. Le script de trace ajoute le vrai tuple k=7, 64 lignes natives et 7394 cas de la trace antérieure. Les coefficients logarithmiques restent symboliques ; les certificats de signe portent seulement sur ces sélections finies. Ces essais n'énumèrent pas le support global à N=10^8, qui est sous l'onset analytique, et n'estiment pas D_N. Leurs reçus déclarent explicitement leur portée finie et la conservation des 190 artefacts antérieurs. Leur replay indépendant demeure la tâche du Juge.

Le faible coût local de N9 reste **par cellule**. La multiplicité extérieure des b,u,v,k,s,t, les facteurs d,e,f,ell, les restes de Rosser, les queues, la variation réelle et R_p doivent être payés. Les fibres minces imposent encore leurs +1. Le moment demandé garde quatre valeurs de Möbius, les deux axes reliés et des fronts mobiles ; il n'est pas le préfixe multiplicatif à petit conducteur déjà acquis au §12.6. Aucun théorème indépendant sur son cumul signé n'a été dérivé par N1–N10.

La candidature échoue précisément au **transfert quantitatif et au raccord natif**, alors que ses identités corrigées sont exactes. Écrire ces identités standard en Lean ne répondrait pas à la condition de victoire. Aucun nouveau .lean facile n'est produit, aucune hypothèse du gain souhaité n'est introduite, aucun diagnostic d'erreur Lean n'est fabriqué. Le Juge doit classer cette piste `REJECTED_BEFORE_COMPILATION`, sans retirer les acquis ni revendiquer une impossibilité générale des caractères.
