# Boucle 8 — Gram bilinéaire de la phase native entière

Agent 2, 2 octobre 2026. Seul ce rapport est écrit. Les audits finaux `round7/agent3_contract_audit.md` et `agent4_contract_audit.md` ont été lus ; aucune pièce acquise, boucle 7 ou donnée Arbor n'est modifiée.

**Résultat :** une information indépendante exacte existe sur le noyau natif complet : son Gram et ses directions exceptionnelles se calculent, y compris les axes nonunitaires et les facteurs principaux composites. La norme bilinéaire qui en résulte ne se transfère pas aux poids HH/raw couplés, ne paie pas les sommes extérieures et n'assure pas la compensation avec le modèle. Aucun mécanisme de victoire ni nouveau fichier Lean auxiliaire n'est proposé.

## Principes et quatre lignes du candidat

L'oscillation native encore disponible est chi(N-h*l)*conj(chi(N)), avec le conducteur provenant de la décomposition originale et ses masques. Elle est une phase de produit suivie d'une translation, et non chi(N-h*l)*conj(chi(h*l)). Sur h*l=0 modulo ce conducteur, elle vaut 1 ; ces points sont précisément un secteur divisible à conserver. Sur les secteurs copremiers, la trace primitive antérieure peut également être principale après multiplication par mu(q). La soustraction du modèle se produit dans la ligne DIV-HARM, pas dans un choix de phase qui l'effacerait.

Le contre-exemple dépassé par le changement de représentation est le tuple k=7 de la boucle 7 : la phase proposée précédemment y était zéro tandis que la ligne native vaut 5/6. La matrice entière ci-dessous garde sa phase égale à 1 et son diagonal, au lieu de demander que les deux axes de m soient unités. L'autre obstacle, non dépassé, est le secteur l=1 de la couverture complète : C1>=N*log(N)/384 éventuellement sur la sous-famille auditée. L'indépendance de l'oscillation résiduelle ne peut donc pas être présumée sur tous les points.

Mechanism: Gram exact de la phase native de produit sur tous les résidus, avec projection des directions exceptionnelles et descente tensorielle composite.
Hypothesis: Une estimation jointe pourrait servir seulement si les vrais poids à quatre Möbius se séparent avec un défaut payé et si la norme ainsi obtenue laisse un gain après diagonales, secteurs constants et coûts extérieurs.
Observable: Contrats exacts de Gram et CRT falsifiables, insertion native complète, puis budget signé indépendant du résidu ; une simple norme du noyau ne suffit pas.
Conflicts: La boucle 7 interdit le remplacement de chi(N) par chi(m), la suppression de DIV et du modèle ; la boucle 6 interdit le gain tiré de la longueur brute et l'oubli des +1.

Ce candidat change la représentation de la phase native, plutôt que seulement son seuil. Son hypothèse quantitative n'est pas affirmée comme un acquis ; l'audit ci-dessous identifie les endroits où elle échoue actuellement.

## 1. Insertion littérale dans la couverture L2

On conserve le profil raw fixé, alpha=ceil(N^(1/4)), Q=floor((N-1)/alpha), m=N-n,

F_N(m)=1_(0<m<N)1_(n>1)1_(gcd(n,N)=1)
 [Lambda(n)-log(n)] [D(m)-W(n,m)],
S_full=sum_(1<=m<N)mu(m)F_N(m).

Aucun détecteur mu(n)^2 n'est ajouté. Les puissances premières propres de n restent présentes. La face alpha*k<m et le préfixe min(Q,floor((m-1)/alpha)) sont littéraux. La couverture L2 déjà auditée donne

S_full=-sum_(h prime,h*l<N,h∤l)
 mu(l)*log(h)/log(h*l)*F_N(h*l).                       (B1)

Les unités, les faces et les noyaux de F_N sont réévalués à h*l ; ils ne deviennent pas des masques constants en l. Pour les n unitaires à N, une ligne DIV avec k|m est automatiquement unitaire à n*N. Par conséquent

D(m)-W(n,m)
=sum_(k<=Q,alpha*k<m,gcd(k,n*N)=1)
 mu(k)*log(k/m)*[1_(k|m)-1/phi(k)].                    (B2)

L'orthogonalité native, sur cette unité, est

1_(k|m)-1/phi(k)
=sum_(chi mod k,chi!=chi0)chi(n)*conj(chi(N))/phi(k).    (B3)

B1–B3 donnent une véritable identité du profil complet, avec h*l<N, h∤l, n=N-h*l>1, gcd(n,N)=1, alpha*k<h*l, k<=Q, gcd(k,n*N)=1, tous les facteurs mu(l),mu(k), fII(n), les logarithmes et la normalisation. Le caractère est exactement chi(N-h*l)*conj(chi(N)). Son prolongement par zéro couvre l'unité au module k, mais ne permet pas de supprimer les autres corrections du profil. Le conducteur primitif q de chi peut diviser k ; il n'est ni automatiquement k, ni le CRT ar.

Dans un développement HH, le même noyau s'insère sur les vrais tuples

A=b*u*v, C=k*s*t, A*x+C*zeta=N,
mu(u)mu(v)mu(s)mu(t), a=u*v*x, r=s*t*zeta.

La phase vaut chi(N-C*zeta)*conj(chi(N)). Les quatre signes, I_W(n), les détecteurs prescrits à HH, les unités, le core, les fronts et log(b)*log(r) demeurent dans son coefficient. Il n'est pas licite de substituer à ce coefficient deux vecteurs choisis. Pour un porteur C_HH et son modèle M_HH, le raccord demeure E_HH=C_HH-M_HH ; B3 ne crée aucune insertion physique dans M_HH. Toute autre correction reste dans sa ligne d'origine.

Les traces primitives OldPq du §5 de la monographie restent acquises : sur gcd(q,m)=1, mu(q)P_q(m)/phi(q)=1/phi(q). Elles ne deviennent pas de nouvelles oscillations par la notation matricielle.

## 2. Contrat exact sur un module premier : tous les résidus

Soient q premier, q∤N, chi nonprincipal modulo q, prolongé par zéro. Pour a,b dans TOUS les résidus F_q, définir

G_chi(a,b)=chi(N-a*b)*conj(chi(N)).                     (B4)

Les lignes a=0 et colonnes b=0 valent 1. Les n nonunitaires donnent la valeur zéro du caractère, conformément à son support natif. On ne filtre pas m=a*b par un masque d'unité ajouté.

Posons w_a=chi(a), y compris w_0=0. Le Gram complet est exactement

sum_(b mod q)G_chi(a,b)*conj(G_chi(c,b))
=q*1_(a=c)-chi(a)*conj(chi(c)),
G_chi G_chi*=q I-w w*.                                (B5)

Preuve : a=c=0 donne q ; a=c non nul donne q-1. Si a=0,c non nul, la somme complète d'un caractère translaté est zéro. Si a et c sont non nuls distincts, factoriser les deux formes affines ; le ratio de leurs racines parcourt tous les résidus sauf 1, et sa somme vaut -1. Le coefficient est chi(a/c). Ces quatre cas donnent B5 sans hypothèse analytique, sans omission d'un secteur.

On a ||w||²=q-1. Le Gram a une valeur propre 1 dans la direction w et q sur son orthogonal. La norme de G_chi vaut donc sqrt(q). Comme G est symétrique, son autre Gram est q I-conj(w)conj(w)*. Pour toute beta complexe sur les q résidus,

||G_chi beta||²=q||beta||²-|sum_b chi(b)beta_b|².       (B6)

Les diagonales q ou q-1 ne sont pas ôtées pour obtenir une moyenne nulle. La somme de Möbius tordue éventuelle apparaît comme un TERME SOUSTRAIT exact du Gram. Si cette somme est petite, la soustraction est petite aussi : cela ne réduit pas automatiquement l'énergie q||beta||² restante. Une petite projection dans la direction exceptionnelle ne prouve pas que toute la direction réelle appartient à un sous-espace de faible norme.

Sur la restriction a,b unités uniquement, la diagonale est q-2 et le Gram devient

G_unit G_unit*=q I-11*-v v*, v_a=chi(a).                (B7)

Les deux directions 1 et v ont valeur propre 1, les autres q. Cette restriction est utile pour identifier les corrections, mais B7 ne remplace pas B5 dans la ligne DIV-HARM : elle perdrait les m nonunitaires. Au q=3, le sous-espace orthogonal aux deux directions peut être vide ; on ne transforme pas ce cas en un gain global.

## 3. Composite carré-libre : facteurs locaux principaux conservés

Pour un module k carré-libre, gcd(k,N)=1, les caractères et B4 se décomposent par CRT en produits tensoriels locaux. Chaque composante nonprincipale chi_p a le Gram B5 et la norme sqrt(p). Une composante locale principale est DIFFERENTE.

Sur tous les résidus modulo p, elle donne

G_0,p(a,b)=1_(p∤N-a*b)=J-P_tilde,
P_tilde(a,b)=1_(a*b=N),

où P_tilde est une permutation sur les unités et zéro sur la ligne/colonne zéro. Sur le sous-espace engendré par delta_0 et le vecteur constant unitaire normalisé, sa matrice est

[[1,sqrt(p-1)],[sqrt(p-1),p-2]].

Sur l'orthogonal, les valeurs singulières sont 1. La norme exacte est

rho_p=((p-1)+sqrt((p-1)^2+4))/2, p-1<rho_p<p.           (B8)

Sur les unités seules, la norme principale locale est p-2. B8 conserve le coût des axes nativement constants. Un caractère global nonprincipal peut avoir de nombreuses composantes locales principales : s'il est induit du conducteur carré-libre q|k, la norme entière est

sqrt(q)*prod_(p|k/q)rho_p <=k/sqrt(q).                 (B9)

Si le caractère est primitif à k, la norme est sqrt(k). Le remplacement de tout caractère induit par une norme sqrt(k), ou de tout facteur principal par sqrt(p), serait faux. Les lignes p|m gardent chi(N) et ne sont pas annulées. Dans le profil N pair, les k unitaires à N sont impairs ; aucune composante interdite de module 2 n'est ajoutée.

Ces identités sont des propriétés indépendantes du noyau natif et de ses diagonales. Les relations générales entre Gauss et Jacobi peuvent aussi les vérifier : [Montgomery–Vaughan, chapitre 9, exercice 9.2.10](https://personal.science.psu.edu/rcv4/personal/Publications/MNTI/13.0_pp_282_325_Primitive_characters_and_Gauss_sums.pdf). Les Gram B5–B9 sont dérivés ici directement ; ils ne sont pas présentés comme un nouveau théorème analytique de parité.

## 4. Borne bilinéaire valide pour des coefficients réellement séparés

Pour des intervalles entiers H,L et des vecteurs alpha_h,beta_l, poser

A_a=sum_(h in H,h=a mod q)alpha_h,
B_b=sum_(l in L,l=b mod q)beta_l.

B4 et B5 donnent exactement, sans supprimer les résidus zéro,

|sum_(h,l)alpha_h beta_l chi(N-h*l)conj(chi(N))|
 <=sqrt(q)||A||_2||B||_2
 <=sqrt(q)*sqrt(1+|H|/q)*sqrt(1+|L|/q)
             ||alpha||_2||beta||_2.                  (B10)

Les +1 paient le nombre maximal de représentants d'une classe dans chaque intervalle. B6 peut garder explicitement le moment exceptionnel au lieu de l'abandonner. Pour des premiers h, alpha peut porter log h et sa norme doit être payée ; pour des beta de Möbius, l'unité h∤l et les masques fixes doivent être conservés. Un masque dépendant de h n'est pas un unique beta fixe pour toutes les lignes.

À q grand et deux longueurs P,L<=q avec P*L~N, le coût bare de B10 est sqrt(q*N), à facteurs logarithmiques près. Pour q~N^.75 et P=L~N^.5, c'est N^(7/8), une amélioration locale réelle sur N. Si P,L>=q, la majoration de classes donne de l'ordre N/sqrt(q), avant les coefficients. Ces chiffres portent sur un bloc séparé, non sur F_N(h*l) entier.

Au cofacteur l=1, |L|=1 et beta n'a aucun préfixe Möbius long. Pour P grand, B10 ne crée pas une annulation du poids entier des premiers. Il ne paie pas le C1 de la boucle 7. Les bornes des blocs longs ne couvrent ni ce point ni tous les secteurs courts.

## 5. Pourquoi le poids réel ne satisfait pas le contrat bare

Dans B1–B3, le coefficient est réellement

mu(l)*log(h)/log(h*l)
 [Lambda(N-h*l)-log(N-h*l)]
 mu(k)*log(k/(h*l)),

avec les fronts, unités, HARM/DIV et la normalisation de B3. Le facteur fII(N-h*l) garde sa structure arithmétique additive, puissances propres comprises. Les faces dépendantes du produit sont encore évaluées à h*l. Des facteurs logarithmiques lisses peuvent être séparés par une intégrale avec son coût ; cela ne sépare pas Lambda(N-h*l), les quatre Möbius du développement HH, la squarefreeness mobile ou les fenêtres originales.

Dans HH, le gelage b,u,v,k,s,t impose A*x+C*zeta=N. Le coefficient mu(u)mu(v)mu(s)mu(t) reste sur cette fibre. La restriction A|N-C*zeta, Hy(a) réel et ses autres termes produisent une matrice COUPLÉE entre C et zeta. Pour C=k*s*t et un conducteur q|k dans DIV, C=0 modulo q ; alors G_chi(C,zeta)=1 pour tout zeta. La matrice complète conserve exactement ce cas, mais aucune oscillation de caractère ne subsiste dans ce secteur. Les quatre vrais signes doivent assurer toute éventuelle cancellation ; B5 ne la prouve pas.

Un contre-exemple exact montre qu'on ne peut étendre B10 à n'importe quel poids couplé borné. Pour chi quadratique, choisir W_ab=G_chi(a,b), réel de module <=1, et alpha=beta=1 sur tous les résidus. Alors

sum_(a,b)W_ab G_chi(a,b)=q+(q-1)^2=q²-q+1,

tandis que la borne bare fournirait q sqrt(q). Pour q>=3, (q²-q+1)^2>q^3. **Ce test falsifie le contrat générique de séparation, pas le poids HH particulier.** Il prouve la nécessité de contrôler le Hadamard W*G réel ou le défaut d'une séparation de ses vrais poids ; un argument qui invoque seulement |W|<=1 est insuffisant.

Dans un carré de Cauchy avec les vrais poids W(C,zeta), le Gram contient

sum_zeta W(C,zeta)conj(W(C',zeta))
           G_chi(C,zeta)conj(G_chi(C',zeta)),

et n'est plus B5. Sa diagonale conserve sum |W|² avec tous les coefficients réels. Le diagonal C=C' inclut toutes les factorisations donnant le même k*s*t, même si les facteurs individuels diffèrent. Il ne peut être remplacé par le diagonal de tuples identiques. L'audit Da/Dk de la monographie reste acquis : supprimer un déplacement ne soustrait pas automatiquement D00, et une grande énergie n'est pas un signe pour le scalaire linéaire.

## 6. Coûts extérieurs, principaux et compensation avec le modèle

Même en accordant un bloc séparé favorable par module k~K et tous ses caractères primitifs, B3 a un poids 1/phi(k) mais jusqu'à phi(k) caractères. Une majoration séparée perd donc l'économie apparente de 1/phi(k). Pour P*L~N et P,L<=k, elle fournit au mieux sqrt(K*N) par k avant logarithmes. La somme absolue sur les K modules d'une bande donne

K sqrt(K*N).

À K~N^.75, cela vaut N^(13/8), avant masques, normalisations et somme des facteurs HH. C'est le coût de cette majoration, pas une borne inférieure sur le vrai signé. Les caractères induits ont B9 et demandent leur propre coût ; une petite dimension primitive n'autorise pas de les abandonner. Garder les k et caractères joints pourrait améliorer ce coût, mais nécessite une estimation nouvelle avec les vrais coefficients mu(k), les fronts et les diagonales. Aucun grand-crible indépendant payé à ce profil n'est dérivé ici.

La projection principale explicitement retirée dans B3 n'efface pas les masses principales physiques. Sur k|m, tous les caractères natifs ont chi(n)conj(chi(N))=1 ; la ligne vaut 1-1/phi(k). Sur le secteur copremier, OldPq peut donner le coefficient constant 1/phi(q) après multiplication par mu(q). Les composants locaux principaux de B8 en rendent le coût visible. Ces contributions restent dans DIV-HARM, et leurs signes ne sont pas ceux d'une énergie positive.

Le modèle M_HH n'est pas généré par le Gram. Il doit être raccordé à C_HH sur les mêmes noyaux et les mêmes faces. Le MAIN continu acquis dans la campagne antérieure n'est pas une borne du vrai selected-root count moins ce MAIN. La nouvelle norme ne contrôle pas leur différence. Les restes de Rosser, queues carrées, nonunités nativement omises et corrections de centrage sont toujours à payer ; les maillages supplémentaires ne peuvent réutiliser une ancienne queue sans ses nouveaux moments.

Enfin, la couverture L2 garde exactement

S_full=-C1+S_rest,
D_N=C1-S_rest+2max(e,0).

L'audit final de boucle 7 donne C1>=N log(N)/384 éventuellement pour N pair, 3∤N, avec seuil global non évalué. B10 n'est pas une estimation de sa compensation par S_rest ; son traitement séparé serait trop cher. Introduire l'inégalité terminale de cette différence comme un nouveau lemme analytique ferait supposer le résultat voulu. La piste indépendante d'Agent 1 examine cette compensation ; le présent rapport ne la remplace pas par une identité matricielle.

## 7. Acquis applicables et obligations encore ouvertes

Les préfixes acquis au §12.6 portent mu(l)*psi(l)*1_(l,K)=1, caractères retenus de petit conducteur, log K<=2u et leurs longueurs/onset. L'onset adaptatif exact est **u>=10^24** : la racine a contrôlé visuellement le PDF original pages 32,33,36 et conservé les rendus et le reçu dans round8 ; l'exposant aplati de l'ancienne extraction ne doit pas devenir u>=1024. N=10^8 est sous cet onset et ne le teste pas. Le facteur chi(N-h*l) est un poids additif de produit, pas automatiquement psi(l). On peut développer cette phase en caractères multiplicatifs modulo un petit premier sur les unités, mais cela garde ses moyennes, ses nonunités et la somme complète des composantes. Le couplage fII(N-h*l), les fronts mobiles et les filtres rough ne disparaissent pas par ce développement.

La norme d'un primorial de rugosité n'entre pas gratuitement dans le masque K<=N². Un masque réellement fixe N*h est dans ce contrat lorsque h<N ; la variation additionnelle et le poids arithmétique mobile ne le sont pas. Aucune extension aux phases mobiles, caractères exclus ou grands conducteurs n'est attribuée aux acquis. Les hypothèses de B5–B10 sont élémentaires ; elles ne supposent ni Goldbach, ni la cible, ni une faible corrélation souhaitée.

Les obligations précises laissées ouvertes sont :

1. Une séparation exacte des vrais poids HH/raw, ou une estimation indépendante de leur Gram pondéré, gardant les quatre Möbius et les diagonales de factorisations.
2. Le coût conjoint des modules/conducteurs et des composantes principales, avec le secteur divisible où la phase vaut 1.
3. Le raccord C_HH-M_HH et tous ses restes au niveau N fixé, sans moyenne sur N ni changement de CRT ar.
4. Les secteurs l=1, zeta=1 et autres fibres courtes, sans paiement absolu incompatible avec le budget.
5. Une compensation signée indépendante au niveau complet, avec le pont e et les constantes terminales, avant toute soumission Lean gagnante.

Il ne s'agit pas de cinq nouvelles hypothèses offertes au compilateur. Ce sont les tâches non résolues par le mécanisme proposé. Aucun gain sur D_N n'est dérivé.

## 8. Contrat de falsification transmis

Pour N=100000000, q=3,7,11,13 (ordre 4 inclus),19, vérifier B5 et B7 sur tous les a,c,b, y compris zéro, les conjugaisons et B6. Les phases restent exactes, jamais flottantes. Pour les modules carrés-libres 21 et 33, vérifier le produit CRT avec deux composantes nonprincipales puis avec une composante locale principale ; garder B8 plutôt qu'une norme sqrt(p) fictive. Le tuple k=7 antérieur garde sa phase native 1 et sa ligne 5/6.

Le falsificateur W=G quadratique vérifie (q²-q+1)^2>q³ en entiers, uniquement pour rejeter l'extension aux poids couplés arbitraires. Les domaines HH/raw et leur signe ne sont pas remplacés par ce banc matriciel. Les fronts h*l<N, h∤l, alpha*k<h*l, zeta=1, l=1, unités et masques restent dans toute insertion de B1–B3.

Retour Agent6 reçu avant ce rapport final : `round8/native_gram.json` déclare PASS de l'algèbre seule, 9339 entrées des Gram premiers, 6120 entrées tensorielles aux modules 21/33, les conjugaisons d'ordre 4, B8 et le falsificateur W=G. Le secteur C=0 modulo7 garde la phase1 et la ligne native5/6. Un diagnostic de mineur raw avec h dans {1,3} ne serait pas un falsificateur de la couverture L2, car h=1 n'y est pas premier ; cette précision a été transmise. Aucune conclusion globale n'est tirée d'un tel petit mineur.

Les formules ont été envoyées à la racine et à l'Agent 6 avant formalisation. Ce rapport n'annonce pas leur replay indépendant par le Juge ni une compilation. Le candidat donne un diagnostic natif exact substantiellement différent du twist perdu de boucle 7, mais **aucun mécanisme quantitatif de contournement de parité n'est obtenu**. Il n'est donc pas proposé d'écrire un fichier Lean standard de remplacement.
