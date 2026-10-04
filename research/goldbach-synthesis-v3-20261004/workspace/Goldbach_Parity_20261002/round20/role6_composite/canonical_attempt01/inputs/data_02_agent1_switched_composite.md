# FINAL1 — boucle20 : soustraction des composites avec premier facteur canonique

Statut FINAL conceptuel : poids inférieur effectivement construit et inégalité d'incidence dérivés sur papier, avant sélection20. Aucun nouveau node, calcul mathématique Python, compilation Lean ou exécution du Juge par ce rôle. Les1808 archives et la prospective immuable sont inchangées. Aucune estimation nouvelle des grands modules n'est démontrée. Une compilation de la seule inégalité ne serait pas une victoire.

## Contraintes, probe et choix

Le skill `arbor-agent-ideate` a été lu. La prospective a utilisé la vue33 findings2583c1 ; après la clôture indépendante19, une nouvelle vue locale a réellement terminé exit0 et été lue entièrement : outil82652e,35 findings,5 directions pruned,maxdepth2,13.11 et14.4 done0. PROBE20 a été lu entièrement à1d62fe avant ce FINAL. Aucun TreeAddNode n'est appelé. Lectures complètes : FINAL1_19, FINAL3_19, revue mathématique19, retour des vrais échecs19 et prospective avec son reçu. Le contrat ancien contient une lecture historique1024 ; la présente note conserve le source corrigé **u=logN>=10^24**. Le texte extrait de la monographie a été consulté notamment autour des sections11–13 ; aucun nouveau statut de preuve n'en est déduit.

PROBE BLOCK

Q1 First principles : **wrong credit assignment / information manquante sur l'incidence double première**. FINAL1_19 K4 et la revue19 section3 donnent Gamma0=Gamma_rank+Pi et montrent la compensation exacte du principal négatif de Pi. FINAL3_19 conserve encore les vrais restes et un M réel ; les corrections des18 FAIL auteurs19 sont des corrections techniques, sans nouvelle hypothèse analytique. Ce sont deux preuves concrètes que le signe d'un prix ou un PASS auxiliaire ne paient pas T_beta.

Q2 Hidden assumption : un majorant positif sur N-crsq, ou une référence plus petite, suffirait à majorer l'incidence réelle relativement à M0. La supprimer impose de conserver une **masse composite réelle soustraite**, sous le même q réellement premier.

Q3 Elephant : les composites dont le premier facteur approche sqrt(j), leurs facteurs répétés et la queue des modules AP au-delà du niveau disponible. Une troncature de poids ne transforme pas cette queue en erreur petite.

Q4 Hamming : oui pour une inégalité portant sur le numérateur réel ; non pour sa seule identité formelle. Il faut comparer le principal dérivé à M0 et payer ses restes avant tout crédit au ledger.

Les quatre mouvements ont été effectués. Inversion : introduire la masse composite avec signe moins au lieu de majorer tout support positif. Raisonnement arrière : la preuve recherchée doit distinguer les candidats premiers et composites sans modifier q. Transfert : utiliser une partition par premier facteur puis une expansion Bonferroni inférieure **construite**, plutôt qu'une hypothèse abstraite de bon poids. Rétro-ingénierie : conserver Gamma_rank/Pi, p² et les fronts de q, puis localiser exactement les modules hors niveau.

Déclaration du survivant prospectif : hypothèse attaquée = crédit provenant du seul majorant positif ; classe = switching par premier facteur avec coefficients de restes AP signés ; chaîne causale = retirer de ce majorant ses composites réels, construire leur minorant pointwise, développer les AP ordinaires et isoler la queue nécessitant une information supplémentaire ; orthogonalité = numérateur T_beta et candidats composites, distincts du prix de référence13.11 et des ressources nonSS14.4 ; conflits = aucune disponibilité, petite Gamma ou masse cible postulée, aucun transport des directions pruned4/6/13.2/1.2/9.2 repris sans défaut.

```text
Mechanism: Soustraction du majorant Selberg sur les candidats composites, partitionnés par p=minFac(j), puis minorant Bonferroni impair construit sur le quotient v et expansion des AP de module p·lcm(h,lcm(k,l)/gcd(lcm(k,l),p)).
Hypothesis: Le poids inférieur Bonferroni construit dérive T_beta(theta)<=P_lambda-C_lambda_minus_main+R_AP-C_large ; la branche réelle p0 soustrait un principal P_lambda/(p0-1) sous q premier, sans changer M0, tandis que le reste et les grands premiers demeurent explicites.
Observable: Preuve pointwise de la somme binomiale réelle, coefficients AP/endpoints dérivés et banque neuve N1e8 sur24m<j<=48m avec tous q physiques premiers, p²/répétitions, cellules négatives non minimales, slack et queue ; principal entier comparé à M0 avant crédit à Gamma.
Conflicts: Le gain de Pi est compensé par Gamma_rank ; M0 reste inchangé ici. Le minorant n'est pas supposé bon, la queue n'est pas effacée, BV ne porte jamais sur beta et aucune compilation de l'identité seule n'est appelée victoire.
```

Ce bloc est une candidature conceptuelle FINAL1 et non un node sélectionné. Le diagnostic du principal, les constantes/onsets et le raccord à tout le ledger sont des gates mathématiques encore ouverts. Le contrat numérique et les signatures proposées ci-dessous ne constituent aucune autorisation d'exécution.

## 1. Objets source conservés

Prendre les paramètres19 et la vraie tranche x/2<j<=x, N/5<=x<=N/4. Pour chaque c<r<s premiers canoniques, conserver d=cr<=a, cs<=a<rs, s<=a, t=crs>a, unités t à N, et toutes les gardes du `PhysicalWitness18`. Le dernier facteur **q est réellement premier**, q>a et q>rs. Le candidat est j=N-tq. Le bulk, M, le front originalQ et les unités q à N restent dans l'intervalle physique J_t. Ils ne sont pas remplacés par un intervalle plus grand dans une somme signée.

La factorisation de t récupère c,r,s dans cet ordre, donc chaque t représente au plus un triple canonique. J_t est un intervalle entier, éventuellement vide, suivi du masque premier et unitaire sur q. Les gardes indépendantes de q restent dans le catalogue des t. Les bornes entières de J_t incluent ceil/floor et tous les +1 ; aucun front X=d(L-1)+1 n'est remplacé par dL.

Écrire kappa_c=logc+S(N), puis

    T_beta(theta)=sum_t kappa_c sum_{q in J_t, q prime, (q,N)=1} theta_N(N-tq).

C'est le numérateur effectif de Gamma0 dans la famille canonique19. Poser M0=F_theta(reference initiale réelle), et conserver Gamma0=T_beta-M0. Le modèle de rang ne remplace pas M0 dans cette note. Le cas A_d=0 reste dans les objets de référence avec sa convention zéro.

Les unités physiques donnent (j,N)=1 et aussi (j,t)=1 : j=N-tq et (N,t)=1. Toute prime divisant j est donc première à tN. Cela permet les suppressions exactes de modules incompatibles ci-dessous, sans annoncer que t et un diviseur quelconque sont automatiquement copremiers.

## 2. Mécanisme rejeté : Selberg positif seul

Fixer t et 1<z<min(j de la tranche). Les coefficients lambda_k sont réels, lambda_1=1, supportés sur les k carrés-libres<=z et premiers à tN. Définir

    S_lambda(j)=(sum_{k|j} lambda_k)^2,
    w_lambda(j)=logj * S_lambda(j).

Sur un candidat premier>z, S_lambda=1. Sur un candidat composite, w_lambda>=0. Ainsi theta_N(j)<=w_lambda(j), sans filtre mu(j)^2 sur la mesure raw.

Le principal AP de la somme en q comporte la forme quadratique exacte

    Q_t(lambda)=sum_{k,l} lambda_k lambda_l /phi(lcm(k,l)).

Sur ce support carré-libre, poser g(k)=1/phi(k), r(e)=product_{p|e}(p-2),

    y_e=sum_{e|k} lambda_k g(k),
    Q_t=sum_e r(e)y_e^2,
    1=lambda_1=sum_e mu(e)y_e.

La seconde identité est l'inversion de Möbius sur l'ensemble fini descendant des k. Cauchy donne le minimum exact

    min Q_t=1/G_t(z),
    G_t(z)=sum_{e<=z, squarefree, (e,tN)=1} 1/r(e).

L'égalité est atteinte par y_e=mu(e)/(r(e)G_t), puis l'inversion fournit les lambda ; elle ne requiert aucune distribution première.

**Diagnostic du coefficient principal, et qualification indispensable.** Pour tN fixé, le coefficient Euler de la croissance logarithmique de G_t est 1/S(tN), avec le vrai produit singulier acquis. Un usage uniforme de G_t(z)~logz/S(tN) lorsque tN croît avec N n'est pas établi ici. Le diagnostic suivant concerne ce principal idéal et les principaux des comptes non masqués de q ; ce n'est pas une borne finie uniforme ni un NoGo de toutes les méthodes.

La revue19 R1 donne

    g0(d)=d/(phi(d)delta_N)*E_h(d,N),
    E_h=product_{p|39,p∤N,p∤d} p(p-2)/(p-1)^2 <=1,
    M_d/A_d=eta_d*g0(d), eta_d=X_d/(dL_d)<=1.

La valeur M_d/A_d s'entend sur A_d>0. Les fibres vides ne reçoivent aucun ratio fictif. Puisque N est pair et (t,N)=1, un calcul exact des facteurs Euler donne

    S(tN)/g0(d)
      = C2/E_h * product_{p odd,p|N} (p-1)^2/[p(p-2)]
                 * product_{p|d} (p-1)^2/[p(p-2)]
                 * (s-1)/(s-2)
      >= C2 >=2541/4096.

Le facteur2 de S(N) est compensé par le facteur1/2 de delta_N ; une borne2C2 serait incorrecte ici. Cette comparaison locale ne postule pas de valeur gratuite de S(N).

Or t>a et q>a impliquent q<N/a<=N^(9/16). Au niveau ordinaire en q, z²<=sqrt(N/t) même avant la marge logarithmique, donc logz<=9u/64. Les candidats j>N/10 ont logj>=u-log10. Le rapport idéal du principal Selberg à celui de la référence est donc au moins

    (2541/576)*(1-log10/u),

strictement supérieur à4 au source. Cette inflation ne peut être payée par le petit chi(P_d) du prix19. Les comptes effectifs A_d, les erreurs PNT/AP et l'uniformité du produit G_t ne sont pas déclarés négligeables : une application source demanderait encore leurs preuves. Le diagnostic suffit à ne pas choisir le majorant positif seul comme promesse de bypass.

## 3. Soustraction exacte des composites avec p² conservé

Pour j>=2 composite, p=minFac(j) est premier, p²<=j, et v=j/p>=p. La condition exacte est

    aucun premier ell<p ne divise v.

**p peut diviser v** : le cas j=p² et tous les facteurs répétés restent présents. Il ne faut pas écrire (p,v)=1 ni P^-(v)>p. Chaque composite est indexé une seule fois par son vrai plus petit premier.

Définir la masse positive réellement présente

    C_lambda=sum_t kappa_c sum_{q physical prime}
                      sum_{p=minFac(j), p²<=j} w_lambda(j), j=N-tq,
    Q_lambda=sum_t kappa_c sum_{q physical prime} w_lambda(N-tq).

Les candidats premiers>z ont w_lambda=theta_N ; les composites sont entièrement retirés. On obtient l'identité effective

    T_beta(theta)=Q_lambda-C_lambda.                         (B1)

Ce n'est pas une nouvelle borne de Gamma. Son intérêt est de produire une masse soustractive à laquelle une information arithmétique indépendante peut être appliquée, sous le q premier inchangé.

## 4. Poids inférieur construit, sans prémisse « xi bonne »

Pour p premier à tN, soit P_{t,p} le produit **fini** des premiers ell<p ne divisant pas tN. Pour v premier à tN, sa roughness correspond à (v,P_{t,p})=1. Choisir K>=0 entier et définir réellement

    xi_{t,p,K}(h)=mu(h) si h|P_{t,p} et omega(h)<=2K+1 ; 0 sinon,
    L_{t,p,K}(v)=sum_{h|v} xi_{t,p,K}(h).

Si r est le nombre de premiers de P_{t,p} divisant v, alors

    L(v)=sum_{i=0}^{2K+1} (-1)^i binom(r,i).

Pour r=0, cette valeur vaut1. Pour r>=1, l'identité de Pascal télescopique donne

    L(v)=-binom(r-1,2K+1)<=0.

La convention binom(n,i)=0 pour i>n couvre aussi les sommes déjà complètes. Par conséquent

    L(v)<=1_{(v,P_{t,p})=1}.                               (B2)

Cette propriété est démontrée par la construction ; elle n'est pas posée comme hypothèse. Le poids peut être négatif sur un quotient non rugueux : aucune positivité de L, de son principal ou de C_lambda_minus n'est annoncée.

Pour une coupe P*, définir

    C_lambda_minus(P*,K)=sum_t kappa_c sum_{q physical prime}
      sum_{p prime, p<=P*, p|j, p²<=j}
        w_lambda(j) L_{t,p,K}(j/p).

Le domaine développé garde tous les p|j admissibles, pas seulement minFac(j). Les p non minimaux reçoivent un poids<=0, et non une ressource positive supplémentaire. Avec C_{<=P*} la vraie masse disjointe B1 de premier facteur<=P*, B2 donne

    C_lambda_minus<=C_{<=P*},
    T_beta<=Q_lambda-C_lambda_minus-C_{>P*}.               (B3)

Le slack exact est positif : pour chaque cellule développée, rough(v)-L(v) vaut0 si r=0, et binom(r-1,2K+1) sinon. Il peut être écrit et vérifié séparément ; il n'est pas masqué par une cancellation de fibre complète.

**Queue explicite.** C_{>P*} garde tous les composites dont minFac(j)>P*, avec p²/répétitions et le même q premier. C'est un crédit négatif encore inexploité dans B3. L'effacer donne une majoration plus faible valide, et ne signifie jamais que cette masse est payée ou petite. Si B_lambda=max_t sum_k|lambda_{t,k}|, le majorant volontairement grossier

    0<=C_{>P*}<=2u² B_lambda² [N(1+u)+N^(9/16)]           (B4)

vient de kappa<=2u, logj<=u, #q<=N/t+1 et de la somme harmonique sur tous les entiers t<N/a. Il n'est pas utilisable au budget terminal. Il rend visible la perte d'amélioration si la queue n'est pas contrôlée ; on ne l'ajoute pas à un autre poste déjà acquis du ledger.

**Branche canonique immédiatement exploitable.** Pour le p0 réel `leastMissingOddPrime N` de16, tous les premiers<p0 divisent N. Sur v unitaire à N, P_{t,p0} est vide et L(v)=1 pour tout K. Si p0 ne divise pas t et p0²<x/2, les candidats p0|j de la tranche sont de vrais composites de premier facteurp0, sans crible inférieur. Cette branche est exacte, et n'exige ni partenaires premiers ni une prémisse de roughness. Si p0|t, elle est vide arithmétiquement. L'adaptation ne re-démontre pas A7 et n'assume pas que p0²<x/2 découle d'un onset non fourni.

## 5. Coefficients AP littéraux et borne de leurs restes

Développer w_lambda par k,l. Pour le composite j=pv, poser

    K0=lcm(k,l), Kp=K0/gcd(K0,p), H=lcm(h,Kp), nu=pH.

Comme K0 est carré-libre,

    K0|pv iff Kp|v,
    h|v et Kp|v iff H|v,
    pH|j iff t*q==N mod nu.                               (B5)

Le quotient Kp est justifié par la divisibilité, pas par une soustraction naturelle tronquée. Les facteurs partagés entre h,k,l restent dans **lcm**, jamais dans un produit supposé copremier. p n'est pas supprimé du module nu ; sa divisibilité à v n'est pas interdite.

Si (nu,tN)>1, la cellule est exactement nulle : soit un facteur commun à t empêche t*q==N, soit un facteur de N empêcherait le candidat unitaire. Sinon t est inversible modulo nu et la classe en q est N*t^{-1} mod nu, réduite. Les p divisant t ou N sont exclus avec cette justification arithmétique.

La fenêtre de q pour C_minus est J_t intersectée avec q<=floor((N-p²)/t). Elle reste entière et peut être vide. Pour une fenêtre non vide [q0,q1] en entiers, q0>a, conserver les endpoints q0-1 et q1. Le poids

    f_t(y)=log(N-ty)/log y

est positif et décroissant sur cette fenêtre continue ; q0-1>=a>1 et N-ty>0. On a f_t<=u/loga<=16/7<3. L'intégrale principale est exactement

    I_t(q0,q1)=integral_{q0-1}^{q1} f_t(y) dy.

Elle n'est pas remplacée par une longueur approximative. Le compte de premiers avec poids logj s'écrit sum f_t(q)*theta(q), en gardant les q divisant N retirés. Pour

    E_theta(Y,nu)=max_{y<=Y,(b,nu)=1}|Theta(y;nu,b)-y/phi(nu)|,

la sommation partielle aux deux endpoints et la variation monotone donnent le reste explicite

    |sum_{q0<=q<=q1, q prime, (q,N)=1, q==N/t mod nu} log(N-tq)
       - I_t/phi(nu)| <=6*(E_theta(Y,nu)+u),               (B6)

avec Y=N/t. Le termeu paie la masse logarithmique totale des premiers q|N avant conversion, pas une erreur imaginaire de Möbius. Si l'on change l'intégrale pour d'autres endpoints, ses fronts supplémentaires doivent être conservés séparément.

Dans Q_lambda, nu=K0 et coefficient kappa_c lambda_k lambda_l. Dans C_minus, nu=p*lcm(h,Kp) et coefficient kappa_c lambda_k lambda_l xi_{t,p,K}(h). Le coefficient exact groupé par nu et fenêtre est la **somme de ces représentations**, avec signe opposé pour C_minus. Aucun plafond32/40/64 issu du prix19 n'est réutilisé comme multiplicité de cette nouvelle expansion.

Noter P_lambda et C_lambda_minus_main les sommes I_t/phi(nu) avec ces coefficients littéraux, et

    R_AP=6 sum_{t,window,nu}|b_{t,window,nu}|*(E_theta(N/t,nu)+u).

On dérive l'inégalité effective

    Gamma0(theta)
      <=P_lambda-C_lambda_minus_main-M0+R_AP-C_{>P*}.     (B7)

B7 est un estimateur quantitatif d'incidence, avec reste AP défini extérieurement ; elle n'a aucune prémisse de petite Gamma. Elle n'affirme pas que R_AP est actuellement payé, que son principal est négatif, ou que cette famille est tout le ledger. Prendre une valeur absolue après regroupement ne permet pas de supprimer les représentations qui ont produit b.

## 6. Où s'arrête l'information ordinaire

La construction donne h<p^(2K+1), Kp<=z² et

    nu<=p^(2K+2)*z².                                    (B8)

Pour tous les t physiques, N/t>a>=N^(7/16). Une condition suffisante uniforme pour le niveau ordinaire, avec sa marge u^{-B}, est

    P*^(2K+2)*z² <= N^(7/32)/u^B.                       (B9)

Le choix K=0 donne log_N(P*)+log_N(z)<=7/64, avant la marge. Il ne garantit pas un principal positif du poids : la somme1-sum_{ell<p}1/(ell-1) devient défavorable sans contrôle supplémentaire. Augmenter K coûte réellement l'exposant2K+2 dans B9. Ce n'est pas une disponibilité gratuite de tous les grands p.

Une autre voie, utilisant un véritable crible inférieur de niveauH sur v plutôt que Bonferroni, aurait besoin de H>p² pour un principal inférieur positif et de p*H*z²<=sqrt(N/t). Elle impose alors p³z²<sqrt(N/t), donc seulement p<N^(7/96) uniformément si z est sous-puissance. Cette condition explique le diagnostic communiqué oralement au coordinateur ; elle n'est pas la condition B9 du poids Bonferroni effectivement construit ici. Le fait que le crible inférieur s'annule pour s<=2 est celui du [lemme2.5 de Matomäki–Zúñiga-Alterman](https://arxiv.org/pdf/2405.19063), pas un nouveau théorème prouvé par cette note.

Les cellules p proche de sqrt(j) demandent nu au moinsp, souvent bien plus. À q<N^(9/16), p procheN^(1/2) dépasse largement sqrt(q). Une autre information arithmétique est donc nécessaire pour extraire leur masse sous q premier. Leur queue reste C_{>P*}, avec B4 seulement comme majorant grossier.

## 7. Mécanisme analytique distinct à investiguer, sans hypothèse équivalente à Gamma

Le prochain axe est le **reste AP signé après switching du premier facteur**, sous la structure factorisée réelle t=crs. Son objet primitif est l'array b dérivé en5, avec q réellement premier et les fenêtres q<=floor((N-p²)/t). Il faut estimer les restes ordinaires portant sur nu=p*lcm(h,Kp), au-delà de leur traitement absolu B9, en exploitant les trois facteurs physiques c,r,s et la primep. Ce changement attaque l'information arithmétique et non la référence.

Un objectif analytique indépendant suffisamment précis pour être réfutable serait : sur chaque bloc dyadique des six coordonnées c,r,s,p,v,q, avec les poids construits exacts et tous les modules incompatibles nuls, démontrer

    |sum b_{t,window,nu} R_theta(N/t,nu,N*t^{-1};window)|
       <=2^40 N^(31/32) u^32.                            (SD, NON PROUVÉ)

Les coefficients, les fenêtres et R_theta sont définis avant de regarder Gamma ; SD concerne des restes de distribution premiers en AP, pas une prémisse « Gamma petite » ou une masse composite postulée. SD reste une cible de théorème nouvelle, très forte, et n'est pas disponible dans les acquis. Ses coefficients signés de roughness ne peuvent pas être remplacés par des poids arbitraires tout en conservant la conclusion. Il faut prouver les bounds de coefficients, séparations Perron/Mellin, nonunités, diagonales et fronts ; écrireSD n'en prouve aucun.

Le récent [Yang, arXiv2608.13299v2 du3septembre2026, lemme3.2 et théorème1.4](https://arxiv.org/pdf/2608.13299) fournit un analogue pour des convolutions et certains poids factorables. Le lemme3.2 impose des inégalités sur les trois niveaux, une composante rough Siegel–Walfisz et un décalage non nul dont dépend la constante. Ici le décalage est N lui-même et les poids du premier facteur sont couplés aux fronts. Aucun résultat à décalage fixe, ni son exposant annoncé, n'est importé pour N croissant. Le papier motive une tentative de réciprocité/Kloosterman ; il ne paie pasSD.

Même siSD était obtenu, il resterait à calculer et comparer **le principal déterministe** P_lambda-C_lambda_minus_main à la référence M0. Supposer ce principal favorable comme remplacement de la cible serait circulaire ; il doit être dérivé des vrais coefficients et intégrales. Une branche qui échoue à cette comparaison doit être rejetée avant formalisation du raccord analytique.

Budget conditionnel vérifiable : six axes dyadiques donnent au plus(3u)^6 blocs pour u>=2, donc au source. SiSD était effectivement démontré uniformément, leur reste total serait<=2^50 N^(31/32)u^38. Relativement à N/(2^20 u ell), son ratio est<=2^70 u^39 ell exp(-u/32). Pour u>=10^24, logu<=sqrtu et logell<=logu donnent un logarithme<=70+40sqrtu-u/32<=-u/64. La perte de puissance paierait donc ce budget au source. **Ce calcul de budget ne prouve pasSD**, ne fournit pas son onset réel et n'efface aucun autre reste.

## 8. Vérifications futures concrètes et mécanismes écartés

Avant une éventuelle sélection20 : fixer z,P*,K et leurs gardes arithmétiques ; prouver B2 pour les vrais ensembles premiers ; exporter les coefficients B5 avant toute évaluation ; calculer le principal et la totalité du reste, y compris la queue ; déterminer si la comparaison à M0 a réellement le bon signe. Le coordinateur doit faire une nouvelle conservation et une sélection après la clôture19. Cette note n'autorise aucun lancement.

Une banque neuve, choisie ensuite, devra garder tous les q premiers physiques, y compris candidats j composites, et distinguer : vrai p=minFac(j) ; toutes les cellules développées p|j,p²<=j ; L(v) négatif éventuel ; le slack Bonferroni ; p², p^e et composites non carrés-libres ; queue p>P* ; AP nonunitaires nuls ; partage des facteurs h,k,l,p et lcm ; fenêtres v>=p aux égalités. Les faux raccourcis à falsifier sont P^-(v)>p, (p,v)=1, h*k*l à la place du lcm, suppression des p non minimaux dans C_minus, principal supposé positif, et reuse du plafond de multiplicité19.

Mécanismes écartés séparément :

- Selberg positif seul : diagnostic2, principal idéal trop grand ; pas de NoGo uniforme établi.
- Nouveau prix de référence négatif : conserve exactement T_beta et accroît Gamma_rank ; rejet comme paiement de Gamma.
- Extension automatique d'un théorème convolution à décalage fixé : SD demanderait uniformité pour le décalageN et les poids couplés ; elle n'est pas fournie par la citation.
- Hypothèse d'une grande masse composite après switching : si elle exprime directement le principal nécessaire à B7, elle ne constitue pas une preuve ; le prochain travail doit viser les restes AP définis indépendamment et la comparaison déterministe.
- Crible inférieur abstrait supposé bon : remplacé par B2 construit ; sa positivité moyenne n'est pas ajoutée comme hypothèse.

## 9. Raw, portée et compte de victoire

Le candidat raw conserve toutes les puissances propres. B1 concerne theta. Le raccord est

    T_beta(raw)=T_beta(theta)+PP_beta,
    Gamma0(raw)=Gamma0(theta)+PP_beta-PP_reference0.

Les poids w_lambda sur les composites retirent également les puissances propres dans B1, comme il convient pour theta ; le raccord raw les réintroduit avec les vrais Lambda. Ni mu(j)^2 sur le raw, ni un second paiement de Bpp acquis ne sont permis.

Le ledger entier reste D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0). Whole U_a incluant r<=alpha, originalQ/k1, vrai S(bN), principal-S(N)N, c1/b1/e1, parents/W, nonSS/T_A, unités/CRT+1, medium/longs, faces/nonbulk, capacités uniques et tous les autres postes restent à raccorder. Aucune identité ici ne les couvre par sous-entendu.

Conclusion mathématique : B2 est un poids inférieur effectivement construit ; B7 est une inégalité d'incidence avec coefficients AP et complément littéraux. Le nouvel apport requis estSD et le signe du principal complet, tous deux ouverts. Aucun PASS Lean, succès numérique, obstacle de parité impossible ou Win n'est déclaré par ce rôle. Le candidat peut être sélectionné comme ingrédient substantiel ; il ne peut être annoncé comme contournement démontré.

## 10. Premier principal composite explicitement positif et compensation du poids

Pour fixer une famille de poids concrète à formaliser, prendre

    K_t(z)={k<=z : squarefree k et (k,t*N*p0)=1},
    G_t^0(z)=sum_{e in K_t(z)} 1/product_{ell|e}(ell-2),
    lambda_{t,k}=mu(k)*phi(k)/G_t^0(z)
                 *sum_{m in K_t(z),k|m} 1/product_{ell|m}(ell-2).

Les lambda sont rationnels réels effectivement définis, lambda1=1, et le minimum quadratique de2 vaut1/G_t^0. Le p0 est le vrai `leastMissingOddPrime N`, pas un premier libre choisi pour son incidence. Une formalisation peut prouver ces propriétés à partir des sommes et des vrais primeFactors ; elle ne reçoit pas lambda1 ou la bonne qualité des poids comme axiomes nouveaux.

Sous l'acquis A7, logp0<=S(N)-1/144 et l'acquis source S(N)<3ell donnent p0<u³. Ainsi p0²<u6<N/10 au sourceu>=10^24 : log(10u6)=log10+6logu<u, par les comparaisons exponentielles élémentaires. La garde p0²<x/2 est donc obtenue pour la tranche source, après raccord à ces acquis. Ceci ne permet pas de déclarer la même garde analytique certifiée par le testN1e8.

Si p0∤t, tous les k,l sont premiers à p0. L'intervalle J_t,p0 est alors exactement J_t et phi(p0*K0)=(p0-1)phi(K0). Le vrai principal positif de la masse composite p0 est

    C_p0_main=I_t *Q_t(lambda)/(p0-1).

Le reste effectif garde les mêmes coefficients lambda_k lambda_l aux AP p0*K0. En sommant les t compatibles, on obtient un retrait **réel** de cette masse, avec R_AP_p0 explicite. Pour p0|t, la branche est nulle ; on ne soustrait pas son principal. Le principal Q_lambda est défini avec le même poids lambda, tandis que M0 reste la référence initiale réelle.

Ce retrait n'est pas un gain net supposé. En omettant p0 de K_t, le coefficient Euler logarithmique de G_t^0 est multiplié par(p0-2)/(p0-1) lorsque p0∤t. Le principal optimal1/G_t^0 est donc gonflé du facteur réciproque, compensé par le retrait1-1/(p0-1). La branche p0 seule ne bat pas le diagnostic idéal de2. C'est un test de cohérence crucial : une masse réellement soustraite peut encore être compensée par le coût du poids. Les couches restantes et leurs restes demeurent le point de recherche.

## 11. Signatures Lean proposées après sélection et gate numérique

Importer les acquis historiques en lecture seule, notamment `leastMissingOddPrime_spec` et les définitions effectives du `PhysicalWitness18`, theta/raw et référence19. Ne pas compiler à nouveau un module acquis inchangé.

1. `oddBonferroniWeight` : définition réelle sur les diviseurs de la primoriale effective ; `oddBonferroni_eq_binomial` et `oddBonferroni_le_roughIndicator` prouventB2 sans prémisse de bon poids. Le r est la vraie cardinalité des premiers communs à v et P_{t,p}, non un entier libre représentant un nombre supposé.
2. `leastPrimeCompositeWitness` : sur les vrais compositesj>=2, p=minFacj est premier, p²<=j, v=j/p>=p, divisibilité effective et aucune primeell<p dansv. Réciproque avec p|j et roughness(v), y comprisp|v ; les p non minimaux appartiennent à l'expansion inférieure avec leurs poids non positifs.
3. `physicalCompositeSubtraction` : B1 sur les vrais q premiers du support physique, et `bonferroniCompositeUpper` : B3 avec C_large et le slack définis comme sommes réelles. Les faux masques mu(j)^2 sur raw et coprimalité(p,v) ne doivent pas apparaître.
4. `compositeAPConductor` : B5 avec vrais lcm/gcd/primeFactors et incompatibilité exacte quand(nu,tN)>1 ; intervalle J_t,p avec p²/fronts et branche vide. Aucun module p*h*k*l incorrect ni multiplicité19 ne sert de raccourci.
5. `leastMissingCompositeLayer` : premier facteur réel p0, primoriale effective vide et branche p0|t nulle, puis facteur principal1/(p0-1) sur la somme phi réelle sous la garde d'intervalle. Le raccord u>=1e24 et la comparaison du principal total ont une portée distincte.
6. `switchedIncidenceEstimator` : B7 avec les remainders AP réellement définis et la queue explicite. Si l'analyse B6 n'est pas encore formalisée, fournir d'abord l'identité exacte principale+reste et sa borne par ces restes ; ne pas ajouter B6 comme faux axiome de Gamma.

Un PASS sans nouvelle information analytique sur les restes ne répond pas à la condition de victoire. L'étude formelle doit rendre l'inégalité et son complément vérifiables, afin que le Juge identifie exactement ce qui demeure ouvert.

## 12. Contrat numérique neuf et complet N=100000000, sans lancement

La fenêtre test est **24000000<j<=48000000**, soit x_test48000000. Elle est disjointe de la banque rank19 à j<=24000000 ; aucun bitmap, ancien résultat ou kernel19 n'est rejoué. Le test de l'identité finie utilise ses gardes générales et ne prétend pas satisfaire x_source<=N/4 : cette garde source est fausse pour x_test, explicitement publiée. Choisir la tranche source x_source=N/4 reste distinct. Toutes les autres gardes physiques sont testées littéralement.

AuN fini : alpha100,Q999999,a3163,M1000000,h39. Prendre **toutes** les paires c<r de premiers unitaires à N, cr<=a, puis tous s premiers avec r<s<=a, cs<=a<rs, t=crs>a, unités t à N ; conserver les triples dont le q intervalle ou le q support premier est vide. Le support de q n'est pas trouvé en filtrant d'abord j premier. Pour chacun,

    q_lo=max(a+1,rs+1,ceil(52000000/t),ceil(M/t)),
    q_hi=min(ceil(76000000/t)-1,floor((N-Q-1)/t)).

L'intervalle prime unitaire à N est exactement q_lo<=q<=q_hi. À chaque q physique, conserver tous les contrôles du vrai `PhysicalWitness18` et j=N-tq. Les c,r,s,q sont distincts et dans leur ordre réel ; les répétitions concernent le candidatj et sont conservées séparément.

Les premiers de facteurs physiques peuvent être construits entièrement jusqu'à11000 : c>=3 et rs>a donnent t>3a et q<76000000/(3a)<11000 ; cs<=a donne s<=a/3. Pour factoriser tous les candidats de la fenêtre, les premiers<=ceil sqrt48000000=6929 suffisent ; ils sont donc également couverts. Le bitmap candidat neuf doit couvrir **les24000000 entiers** de la fenêtre, y compris nonunités et nonpremiers. Sa complétude est justifiée par les diviseurs jusqu'à sqrt48000000. Les factorisations nécessaires aux images physiques sont intégrales, avec multiplicité, et non déduites d'un faux test « non détecté premier ».

Conserver z_source=ceilN^(1/64),P_source=floorN^(1/64),K_source=1 comme coupes arithmétiques nouvelles dont les gardes source devront être démontrées : p^4z²<=4N^(3/32), sous la garde de ceil, laisse une marge sous N^(7/32). AuN fini, z_source=2 et P_source=1 ; la couche inférieure source est vide et aucune positivité de principal ou onset n'est déclarée. **Les coupes test sont z_test=11 et19, P_test=17, K_test=0 et1**, distinctes des coupes source. Leur seul objet est d'exercer les vrais poids/overlaps/slack ; elles ne certifient pasSD ou un budget.

Le futur producteur calcule p0 réellement, puis les lambda_t rationnels de10 sur le support carré-libre premier à t*N*p0. Il conserve lambda1, toutes les valeurs nulles, G et Q=1/G comme fractions exactes. Chaque k original avec mu=0 dans un catalogue étendu est explicitement nul ; il ne crée pas une capacité. Les candidats ont j>z_test ; les branches v=p et p|v ne sont pas omises.

Exigences de sortie complète :

- Catalogue de tous les t, triples canoniques, q_lo/q_hi, q réellement premiers et unitaires, cellules vides, imagej et factorisation complète. Les labels contiennent tous les q physiques, pas seulement les6304 ou un autre compte historique d'images premières.
- Sur chaque candidatj physique : prime/composite/properpower, vraie minFacj, toutes les cellules p|j,p²<=j développées, v=j/p, liste des premiers de P_{t,p} divisantv et r, L(v) exact, roughness(v), slack exact et queue p>P_test/P_source. Les p non minimaux ne sont pas supprimés ; les cellules négatives restent signées.
- Pour chaque combinaison z,P,K : identité B1 par **cartes de coefficients rationnels des vrais logj** avant toute évaluation logarithmique ; B3 avec C_true_low-C_minus=slack>=0 et C_large séparé ; aucun signe de C_minus ou Gamma n'est présupposé. Les properpowers gardent logj dans w_lambda pour theta et log(basepremière) dans le raccordraw.
- Registre AP complet de tous k,l et tous h effectivement présents dans xi, même si h ne divise aucun v de la fenêtre ; module nu réel, classe N/t réduite ou preuve d'incompatibilité, coefficient regroupé, p²-cap exact, fenêtre vide/pleine. Vérifier B5 et les bounds B8 avec les **fronts+1 conservés**. Les modules supérieurs à Y gardent leur principal et leur reste ; aucun « aucune prime observée » ne les supprime.
- AP de Q et de C_minus calculées avec q premier **non masqué par j premier**. La somme exacte avec poids logj est une carte de coefficients prime-logj rationnels. Pour le modèle, I_t est entourée rigoureusement par bornes monotones rationnelles de f_t sur un maillage rationnel : toutes les valeurs log sont entourées vers l'extérieur, chaque borne intégrale reste valide. Raffiner si nécessaire pour le signe ; si une comparaison du principal reste indécidable, publier la largeur et le statut distinct, sans transformer cette indécision en identité fausse ou budget payé.
- Pour chaque classe AP utilisée, les restes theta(q) d'endpoints et leur maximum sur la classe sont certifiés aux sauts premiers, à leurs limites gauches et à Y, avec les q divisantN retirés séparément. Les classes nonunitaires nulles sont justifiées arithmétiquement. Les valeurs globales E_theta source sont des objets analytiques ; une erreur de classe finie ne s'appelle jamais un théorème BV.
- Calculer M0 littéralement avec la convention U0={(b,N*h)=1} sur **tous les b entiers** de chaque d=cr<=a, y compris les fibres A_d=0. Pour la fenêtre test, b_min=ceil(52000000/d),b_max=ceil(76000000/d)-1 et X=d(L-1)+1. Garder les changements unitaires de19 seulement comme références immuables, sans les re-produire ni les utiliser pour un nouveau crédit. Publier T_beta, Gamma0=T_beta-M0 et le nouveau principal P_lambda-C_minus_main-M0 avec leurs erreurs et queue.
- Conserver la dépendance kappa_c=logc+S(N) : cartes affines en S(N) sur l'enclosure acquise auN fini [2541/1536,11011/6144], sans fournir une valeur gratuite de S. La banque certifie POS/NEG/ZERO seulement quand ses enclosures rigoureuses le permettent ; aucun float, log machine ou signe implicite n'est accepté.
- Énumérer tous les properpowers de la **nouvelle** fenêtre par bases premières/exposants, puis PP_beta et PP_reference0. Vérifier le raccordraw complet de9 et publier toute branche où ils sont nuls. Aucun mu(j)^2 sur raw, aucune disparition de p² dans C et aucun second paiement au Bpp acquis.
- D/W/wholeUa/Q et leurs prix parent restent dans le ledger source ; aucune banque de noyaux19 ou d'anciens PASS n'est relancée. Le présent contrat porte sur T_beta/reférence et la nouvelle soustraction, sans prétendre avoir évalué les postes W/parents restants ou toutD_N.

Falsificateurs nouveaux obligatoires : remplacer P^-(v)>=p par P^-(v)>p ; imposer(p,v)=1 ; rendre L(v) positif sur tous les quotients ; compter seulement p=minFacj dans C_minus ; remplacer le lcm par un produit ; supprimer la queue ou les modules>Y ; remplacer le candidat logj de w_lambda par log(base) ; oublier PP au raccordraw ; traiter la garde x_source pour x_test comme vraie ; annoncer le retrait p0 comme crédit net sans le coût Euler du poids. Pour chaque simplification fausse, chercher un contre-exemple dans le domaine complet. En l'absence de témoin physique, publier NONE_IN_DOMAIN, et vérifier séparément les cas limites locaux tels quej=p² sans inventer une incidence auN fixé.

Les intégrales/logs peuvent demander des enclosures plus larges que les cartes exactes d'identité. Une identité vraie n'est pas tuée par une borne d'erreur peu précise ; un signe ou une inégalité numériquement réfutés sont publiés avec leur témoin et tuent la promotion correspondante avant Lean. Ce contrat n'autorise aucun producteur : sélection, full-source review et gate root distincte restent nécessaires.

## 13. Portée FINAL et obligations non payées

Ce FINAL apporte un système de poids **construit**, une vraie masse composite soustraite sous q premier, le slack/complément et une dérivation des coefficients AP et de l'erreur par variation. Il isole un premier principal composite positif et montre aussi pourquoi son retrait ne crée pas automatiquement un gain net. C_minus inconnue ouSD écrite ne sont jamais employés comme acquis.

Restent ouverts : application source avec les constants/onsets effectifs des erreurs AP ; estimation nouvelleSD sous les poids couplés et le décalageN ; signe du principal complet ; masse hors niveau/slack et optimisation qui dépasse la compensation ; Gamma entière, familles hors de cette extraction, parents/W, medium/long, nonSS/T_A, capacités uniques et ledger entier. Les1808 archives sont protégées. Score conceptuel0, victoryfalse, aucune compilation ou production numérique parROLE1.
