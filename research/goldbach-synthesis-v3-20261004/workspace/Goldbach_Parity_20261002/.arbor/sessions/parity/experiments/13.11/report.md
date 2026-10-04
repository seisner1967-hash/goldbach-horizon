# FINAL1 — calibration de rang sur l'agrégat canonique entier, boucle 19

**Résultat conceptuel nouveau : un principal négatif explicite pour le prix entier d'une calibration sensible au rang, avec réduction de ses erreurs à des progressions premières de modules de taille N^(15/32) et à des pertes absolues de puissance.** Le prix inclut le changement des conventions d'unités. Il s'agit d'une estimation de fonctionnelle physique première, pas d'une nouvelle norme ni d'un témoin Type II présenté comme impossibilité de Gamma. Le résidu Gamma corrigé, le côté parent et le ledger restent non estimés. Aucune victoire, aucune compilation ni production numérique n'a été exécutée par ce rôle.

```text
Mechanism: Retirer simultanément la face P|(N-j), P=7·11·23, impossible pour toutes les images canoniques crsq, puis calibrer chaque vraie fibre sur les unités hors de cette face ; séparer les exclusions unitaires p|d à R et comprimer leurs modules AP par la factorisation effective de d*k.
Hypothesis: Le défaut de rang fournit un prix Gamma(theta) de principal strictement négatif pour tous les conducteurs, même partageant P ; les grandes exclusions coûtent au plus u fois leurs entiers perdus et les petites n'engendrent que 64 représentations par module de taille 39P·max(aR,R^4).
Observable: Identité entière Gamma_0=Gamma_rank+Pi, principal Pi=-sum kappa_c M_d chi(P_d), chi_min=451/2336400 ; borne indépendante des erreurs AP/fronts/unités, prix raw-properpowers distinct et banque neuve N=10^8 sur tous c<r premiers unitaires, cr≤3163, candidats 12000000<j≤24000000.
Conflicts: Le diagnostic adversarial global seul est rejeté ; la présente estimation concerne le prix réel theta/raw de toutes les fibres canoniques considérées, sans disponibilité première, petite Gamma ou cible postulée ; Gamma_rank, parents, onset BV et tous les autres postes du ledger restent ouverts.
```

## 1. Entrées, probe et filtrage

J'ai lu en entier PROBE19, feedback18, FINAL1/3/5 et revue de contenu18, FINAL1_15 et les deux mécanismes rejetés12. Une vue fraîche des contraintes a réellement été lue en UTF-8 :33 findings,5 directions pruned,maxdepth2. La première lecture du helper a rencontré seulement un UnicodeEncodeError de stdout cp1252 ; la lecture UTF-8 a ensuite terminé exit0. Ce n'est ni un test mathématique ni un échec Lean. Le skill arbor-agent-ideate est appliqué ; aucun node n'est ajouté par ce rôle.

Q1 — **Mauvais crédit et mauvaise représentation des prix.** Le reçu18 donne JR=234 pour H et JR=0 pour H*11, tandis que le prix bilinéaire conserve exactement toute l'ancienne somme ; l'annexe CRT refuse R5 sous les gardes faux/vrai/faux. Le Juge18 confirme en outre que les vrais prix theta, raw et II sont distincts et que la covariance agrégée reste ouverte. Ces deux faits interdisent d'interpréter une suppression de support comme un paiement.

Q2 — **Hypothèse cachée retirée.** Il n'est pas nécessaire de traiter toute suppression de référence comme une erreur absolue sans signe. Une sélection impossible pour les images physiques peut être surreprésentée dans la mesure première de la référence, et son prix normalisé peut alors avoir un principal négatif indépendant. Ce signe doit être dérivé pour la vraie theta, avec ses erreurs, et pas transféré d'un coefficient adversarial.

Q3 — **Elephant.** Les unités à d font apparaître des modules d², parfois bien au-delà de sqrt(N). Il serait incorrect de citer BV après ce changement sans traiter les grands facteurs de d. Les normalisations J et J' et le partage de P par d doivent également être conservés.

Q4 — **Hamming : oui pour un prix effectivement présent.** La fonctionnelle Pi entre littéralement dans l'identité de Gamma entière. Sa majoration par un principal négatif et son contrôle d'erreur peuvent fournir un crédit réel à une future comparaison parent-image. Ils ne donnent pas, seuls, la borne du résidu.

Les quatre mouvements ont été effectués. L'inversion cherche le signe du prix plutôt qu'une référence qui paraît petite. La recherche depuis une réussite demande une réduction aux seules AP non masquées, sans seconde incidence première comme prémisse. Le transfert analogique est une stratification par rang : trois petits facteurs sont incompatibles avec une image qui n'en possède que deux. La rétro-ingénierie conserve les prix18 et traite séparément les unités dont les modules dépassaient le niveau disponible.

Candidats rejetés avant soumission :

- Une projection Gram supplémentaire et une compression MM/DM sans estimation arithmétique ne paieraient toujours aucune covariance ;12.1 le conserve déjà.
- Une identité de Vaughan ordinaire sur le candidat, sans estimation nouvelle de sa queue, déplacerait la parité dans un autre coefficient. Elle n'est pas retenue.
- Un témoin Type II global sur la face de rang3 serait un diagnostic nouveau par rapport à la fibre18, mais pas une estimation de Gamma(theta). Il n'est pas le mécanisme sélectionnable ici.
- Une calibration par l'union des petits premiers ne serait que la généralisation du déplacement18. Le survivant retire une seule intersection de rang3, calcule le vrai principal du prix et estime aussi tous les changements d'unités.

Déclaration à cinq champs du survivant : hypothèse attaquée = prix sans signe ou unités d gratuites ; classe = calibration arithmétique de rang et séparation des facteurs du conducteur ; chaîne causale = impossibilité physique de la face, biais premier 1/phi(P_d) supérieur au biais entier 1/P_d, puis principal négatif et erreurs AP/front/large facteur explicites ; orthogonalité = estimation de la fonctionnelle première entière du prix, distincte de la capacité non-SS et du témoin universel18 ; conflits = aucune face du ledger n'est supprimée, aucune correction raw n'est cachée, les cinq directions pruned n'offrent ni noyau invariant ni petite covariance et ne sont pas réutilisées comme axiomes.

## 2. Objets physiques et agrégat complet considéré

Conserver u=log N, ell=log u, alpha=ceil N^(1/4), Q=floor((N-1)/alpha), a=ceil N^(7/16), M=ceil N^(3/4), N pair et le source u≥10^24. Choisir x entre N/5 et N/4. La tranche candidate est x/2<j≤x. Pour chaque paire de premiers c<r, (cr,N)=1, d=cr≤a, prendre **toutes** les fibres, y compris A_d=0, et

    I_d={b entier : x/2<N-db≤x}, L_d=#I_d,
    n_lo=min{N-db:b∈I_d}, n_hi=max{N-db:b∈I_d},
    X_d=n_hi-n_lo+1=d(L_d-1)+1 lorsque L_d>0.

Les bornes entières sont b_min=ceil((N-x)/d), b_max=ceil((N-x/2)/d)-1. Au source la tranche est bulk et j>Q ; pour un contrat général les gardes M≤db et db+Q<N restent explicites. Il ne faut pas remplacer X_d par dL_d.

Le masque beta_d(b) est exactement le masque physique18 : vrais premiers c,r,s,q, c<r<s≤a<q, b=sq, cr,cs≤a<rs<q, crs>a, unités crsq à N, bulk et front original. Il ne teste pas j premier. Chaque image est canonique et comptée une seule fois par (c,r,b). Tous les paramètres tardifs restent présents.

Poser h=39, kappa_c=log c+S(N)>0. Les unités de référence initiales sont U_d^0={b∈I_d:(b,Nh)=1}. Elles sont celles d'une des deux conventions explicitement gardées depuis15–18. Les unités finales sont U_d={b∈I_d:(b,Nhd)=1}. beta est supporté sur les deux, puisque les facteurs s,q dépassent tous les premiers de h quand 13²≤a. Le cas h partageant d ou N n'est pas supprimé.

Pour un ensemble U, écrire A_d=sum beta_d, J=#U, B_U=(A_d/J)1_U avec quotient nul si J=0. A_d≤J. Le profil initial z_d^0=beta_d-B_U0 et l'agrégat

    Z_0(j)=sum_d kappa_c z_d^0((N-j)/d)

gardent la garde entière d|(N-j), (N-j)/d∈I_d avant toute division. Gamma_0(theta)=sum_j Z_0(j)theta_N(j). rawLambda_N(j) est le vrai von Mangoldt unitaire sans mu(j)².

**Cet agrégat est entier sur la famille canonique extraite15, avec toutes ses fibres et tous ses prix. Ce n'est pas la totalité des termes du ledger, ni un remplacement des cofacteurs extérieurs.**

## 3. Face globale de rang3, sans séparation de lignes

Fixer trois premiers distincts p1,p2,p3, chacun p_i²≤a, et (P,Nh)=1 pour P=p1p2p3. Dans la branche quantitative explicite on prend p1=7,p2=11,p3=23, P=1771 ; la condition (P,N)=1 est une garde annoncée, pas une propriété de tous N pairs.

Dans toute image crsq, r<s et rs>a donnent s²>a, et q>a donne q²>a. Un premier p avec p²≤a divisant crsq doit donc être c ou r. Trois premiers distincts de cette taille ne peuvent tous diviser crsq. Par conséquent

    P|m et d|m  =>  beta_d(m/d)=0 pour TOUT d de la famille. (K1)

Ce fait ne demande aucune incidence première, aucune A_d positive et aucune largeur V<d. La garde d|m est obligatoire avant le quotient ; les autres d contribuent zéro par la garde de progression du profil. Il dérive des vrais facteurs physiques, pas d'un masque arbitraire. Sur la face F={j:P|(N-j)},

    Z_0(j)=-sum_d kappa_c B_U0((N-j)/d)≤0,
    Gamma_0(theta;F)≤0 et Gamma_0(raw;F)≤0.               (K2)

Les deux mesures sont positives ; raw n'est pas filtré par mu². K2 donne un signe unilatéral réel, mais ne borne pas la partie hors F.

Poser P_d=P/gcd(P,d). Puisque P est squarefree et d est le produit de deux premiers distincts,

    P_d>1, (P_d,Nhd)=1,
    P|db <=> P_d|b.                                      (K3)

Cela inclut d partageant zéro, un ou deux des trois premiers : d39 donne P_d1771 et recouvre h ; d91 donne P_d253 ; d77 donne P_d23 ; d161 donne P_d11 ; d253 donne P_d7. Ces exemples sont des cas de structure de conducteur, sans A_d positive annoncée. Définir U_d'=U_d\{b:P_d|b}, J_d'=card U_d', et B_d'=A_d/J_d' 1_Ud'. Le support physique est contenu dans U_d', donc A_d≤J_d'. **Si J_d'=0, alors A_d=0** et toutes les références/prix de cette fibre sont nuls. Aucun quotient positif ou non-vacuité n'est fabriqué.

## 4. Prix exact et raccord aux deux conventions d'unités

E_d[theta]=F_theta(B_Ud-B_U0) est le prix unitaire antérieur. L_d^F[theta]=F_theta(B_d'-B_Ud) est le nouveau prix de rang. Leur somme est le prix complet

    Pi_d[theta]=F_theta(B_d'-B_U0)=E_d[theta]+L_d^F[theta],
    Gamma_0(theta)=Gamma_rank(theta)+sum_d kappa_c Pi_d[theta]. (K4)

Gamma_rank est construit sur beta_d-B_d', sans suppression de candidats ou de prix. Pour J,J'>0, T=sum_U theta, T_F=sum_(U,P_d|b)theta et J_F=#(U,P_d|b),

    L_d^F=A_d [(T-T_F)/J' - T/J]
         =A_d (J_F T-J T_F)/(J J').                      (K5)

K5 est littéral. Le signe du prix mesuré n'est pas annoncé avant ses erreurs. Sa direction principale vient du biais premier de la classe retirée, pas de la nullité de II_prime du tour18.

Toutes les corrélations DD-DM-MD+MM demeurent. Si D(j) est la somme des masques pondérés et M_0/M_rank les références agrégées, Z_0=D-M_0=Z_rank+(M_rank-M_0). Dans un moment à deux produits, cette égalité conserve DD, les deux termes mixtes et MM, puis les deux interactions avec le prix et le carré du prix. **Aucune petite énergie, positivité du Gram ou annulation de ces termes n'est affirmée.** L'estimation ci-dessous porte sur la fonctionnelle theta réellement présente dans K4.

## 5. Variation normalisée : grandes exclusions réellement payées

Lemme de moyenne avec support réel. Soit V⊂U, beta supporté sur V, A=sum beta≤#V. Pour u≥0, 0≤f≤u sur U et références normalisées B_U,B_V,

    |F_f(B_V-B_U)|≤u A #(U\V)/#U≤u #(U\V).              (K6)

Si V est vide, A=0 et le membre gauche est0. Sinon écrire les deux moyennes séparant V et U\V : leur différence est A·#(U\V)/#U fois la différence de leurs moyennes, dont l'écart est≤u. Ce facteur exact est conservé ; un changement de normalisation n'est pas gratuitement borné par les seuls poids supprimés.

Choisir un entier R≥1 et d_s=produit des p|d avec p≤R. U_s utilise les unités à H_s=Nh d_s. U_s' retire la même face P_d|b. Passer de U_s' à U_d' retire au plus

    J_lost≤sum_(p|d,p>R) (L_d/p+1)≤2(L_d/R+1).         (K7)

C'est une majoration d'entiers dans l'intervalle ; aucune AP première n'est utilisée. K6 avec f=theta_N≤u donne

    |Pi_d-Pi_d^s|≤2u(L_d/R+1),
    Pi_d^s=F_theta(B_Us'-B_U0).                         (K8)

La première référence initiale est la même, donc il n'y a qu'un changement unitaire dans K8. Toute unité grande et son front+1 sont payés. Après kappa_c≤2u et sum L_d≤N(1+log a)+a,

    sum kappa_c |Pi_d-Pi_d^s|
       ≤4u²[N(1+u)/R+a/R+a].                           (K9)

Pour R=ceil N^(1/32), a≤2N^(7/16), u≥1, ce coût est au plus

    8N^(31/32)u³+16N^(7/16)u².                         (K10)

K6–K10 sont des estimations indépendantes des incidences premières masquées. Elles sont la réponse au défaut d² laissé par les prix unitaires.

## 6. Les petites exclusions produisent des modules factorisés courts

Sur un candidat n réellement premier et unitaire à N, avec d unitaire à N, b=(N-n)/d est automatiquement unitaire à N. Il suffit donc, pour la somme theta des références, de développer les unités à rad(h d_s) en retirant les premiers divisant N. Poser

    e_s=rad(h d_s)/gcd(rad(h d_s),N),
    a_s(d)=sum_(k|e_s) mu(k)/phi(dk),
    delta_s=phi(H_s)/H_s, eta_s=sum_(k|H_s)|mu(k)|.

Les diviseurs mu=0 ne doivent pas être effacés des listes originales. Les produits d*k viennent réellement de k|b et db=N-n ; ce sont des AP de résidu N modulo d*k, avec (N,dk)=1. Pour la face, le module est d*k*P_d. Comme (P_d,e_s d)=1,

    T_s=X_d a_s(d)+error_s,
    T_F,s=X_d a_s(d)/phi(P_d)+error_F,s.                (K11)

Pour h=39, écrire k=t*k_s avec t|39, k_s|d_s et (k_s,39)=1. Si k_s contient un seul premier de d, d*k_s≤aR ; s'il les contient tous les deux, d≤R² et d*k_s=d²≤R⁴. Donc tous les modules sont≤

    Q_R=39P max(aR,R⁴).                                (K12)

Le même plafond couvre T_0. Ce n'est pas la borne incorrecte aR². Pour le R source et les ceils, Q_R≤624P N^(15/32) dès les gardes source élémentaires.

**Multiplicité effective.** Un entier d*k_s a deux facteurs premiers distincts, chacun d'exposant1 ou2. Sa factorisation retrouve d et k_s : les facteurs d'exposant2 sont exactement k_s. Pour un module q final, retirer un facteur fixe f|39P laisse donc au plus une représentation (d,k_s). T_s a au plus4 choix f, T_F,s au plus32, T_0 au plus4, soit au plus40 contributions développées ; la borne64 est conservatrice. Cela comprend le partage de P par d et les premiers3/13 dans d ou N. Il ne s'agit pas d'une multiplicité analytique arbitraire promue en capacité physique.

Soit E_theta(N,q)=max_(t≤N,(v,q)=1)|Theta(t;q,v)-t/phi(q)| pour la somme non masquée sur les vrais premiers. Chaque intervalle n_lo..n_hi conserve ses deux erreurs d'endpoints≤2E_theta. Pour theta_N, les premiers divisant N sont retirés explicitement. Leur masse totale est≤sum_(p|N)log p≤u. Il y a au plus16 termes IE pour chacun T_s,T_F,s, et4 pour T_0 ; l'exception totale pondérée est≤144N^(7/16)u².

Les coefficients de chacune des références physiques sont≤1 parce que beta est supporté dans son unité réelle, y compris hors face. La multiplicité64, les deux endpoints et kappa≤2u donnent

    erreur_AP_pondérée≤256u sum_(q≤Q_R) E_theta(N,q).   (K13)

Aucun BV n'est appliqué au masque beta, à deux incidences premières ni à Gamma_rank. K13 concerne exclusivement ces progressions non masquées de la référence.

## 7. Principal : invariance des unités à d et signe de rang

Pour tout premier p|d, ajouter l'unité p∤b multiplie la densité entière par (1-1/p). Dans a_s(d), phi(dp)=p phi(d) produit **le même facteur**. Ainsi

    a_s(d)/delta_s=a_0(d)/delta_0,                     (K14)

où H_0=Nh et e_0=rad(h)/gcd(rad(h),N). Les facteurs de h déjà dans d ou N sont traités une seule fois. Le principal du prix unitaire est zéro ; K8–K13 conservent ses écarts effectifs. K14 ne rend pas le prix mesuré nul.

Le compte entier par IE/CRT donne

    |J_s-L_d delta_s|≤eta_s,
    |J_F,s-L_d delta_s/P_d|≤eta_s,
    |J_s'-L_d delta_s(1-1/P_d)|≤2eta_s.                (K15)

Ces formules ont des classes uniques car (P_d,H_s)=1. Poser

    M_d=A_d X_d a_0(d)/(L_d delta_0),
    chi(t)=(t-phi(t))/(phi(t)(t-1))>0, t=P_d>1.

K11,K14,K15 donnent le principal

    Pi_d^principal
      =M_d[(1-1/phi(P_d))/(1-1/P_d)-1]
      =-M_d chi(P_d).                                 (K16)

Le ratio premier 1/phi(P_d) est supérieur au ratio entier1/P_d. Pour un seul premier restant, chi(p)=1/(p-1)² ; pour zéro partage, on retire une intersection de trois classes, pas leur union. Les sept valeurs possibles de P_d sont7,11,23,77,161,253,1771. Leurs chi sont respectivement

    1/36, 1/100, 1/484, 17/4560, 29/21120,
    11/18480, 451/2336400.

Le minimum exact est chi_*=451/2336400 ; les comparaisons sont des produits croisés d'entiers. Aucun logarithme ou test empirique n'est nécessaire à ce signe.

Si L_d≥2, X_d≥dL_d/2. Les facteurs locaux de h donnent

    a_0(d)/delta_0
      ≥(1/phi(d)) (3/4)(143/144)
      =(1/phi(d))143/192.

Pour p|h partageant d, le facteur est1 ; s'il partage N il est absent ; sinon il vaut p(p-2)/(p-1)². Le facteur 1/delta_N≥1 ne baisse pas cette borne. Donc M_d≥143A_d/384. Avec la masse structurelle réelle Acal=sum kappa_c A_d,

    sum kappa_c M_d chi(P_d)
      ≥ C_* Acal, C_*=64493/897177600.                 (K17)

Acal n'est jamais remplacée par une densité inférieure postulée. Une famille vide donne Acal=0 et prix0.

## 8. Borne écrite entière et limites de source

Garder les gardes arithmétiques indépendantes L_d≥2, L_d delta_s≥4eta_s, L_d delta_0≥4eta_0 pour toutes les fibres. Au source, la preuve factorielle écrite18 donne delta_s,delta_0≥1/u et eta_s,eta_0≤N^(1/16), car H_s,H_0≤N² ; cette application n'a pas encore été certifiée sous Lean dans18. Les vrais fronts donnent L_d≥N^(9/16)/40. Ces gardes découlent alors des mêmes comparaisons exponentielles contre polynômes, sans disponibilité première.

Les erreurs de normalisation sont conservées. Pour rho_0=A/J_0 et r_0=A/(L delta_0), |rho_0-r_0|≤eta_0/(L delta_0). Pour la référence hors face, |rho_s'-r_s'|≤3eta_s/(L delta_s), puisque P_d≥7. Le principal de T_s-T_F,s et celui de T_0 sont≤3L_d pour d produit de deux premiers impairs ; d/phi(d)<2 suffit. Après kappa≤2u et card{d}≤a, le coût de ces fronts est≤48N^(1/2)u².

En combinant K9–K16 et les exceptions N, pour le **prix combiné entier** Pi=sum kappa_c Pi_d(theta),

    |Pi + sum kappa_c M_d chi(P_d)| ≤ B_price,
    B_price=256u sum_(q≤Q_R) E_theta(N,q)
            +48N^(1/2)u²+8N^(31/32)u³+160N^(7/16)u². (K18)

D'où la véritable inégalité unilatérale

    Pi≤-C_* Acal+B_price,
    Gamma_0(theta)≤Gamma_rank(theta)-C_* Acal+B_price.  (K19)

Il ne s'agit pas d'une borne de Gamma transformée en prémisse. Les objets nouveaux à estimer dans B_price sont les erreurs AP ordinaires indépendantes ; les fronts et grandes unités ont des majorants écrits explicites. Gamma_rank ne figure dans aucune hypothèse de K18 et reste littérale dans K19. Elle peut augmenter précisément du montant opposé au prix négatif : aucun gain net n'est déduit de la calibration tant que cette nouvelle covariance n'est pas estimée indépendamment.

J'ai vérifié la source primaire [Goldston–Graham–Pintz–Yıldırım, pages2–3, équations1.5–1.7](https://arxiv.org/pdf/math/0506067). Leur énoncé BV porte sur le poids premier logarithmique et une erreur dyadique maximale. Le passage à E_theta cumulative conserve K_N=ceil(u/log2)+1 et la queue1/phi(q), comme au raccord15. Il exige Q_R≤sqrt(N)/u^B et un onset supplémentaire, avec constantes non calculées. L'exposant15/32 laisse une marge pour chaque B fixé, mais **aucun paiement certifié au seul u≥10^24 n'est annoncé**. Ce contrôle qualitatif n'est pas une formalisation Lean d'AP ; il ne couvre pas une famille avec P|N, ni ne prouve Gamma_rank petite.

## 9. Raw : signe de face et correction properpowers séparée

K1/K2 s'appliquent à rawLambda_N≥0. Pour le prix complet,

    Pi(raw)=Pi(theta)+PP_price,
    PP_price=sum_j [M_rank(j)-M_0(j)]
                         [rawLambda_N(j)-theta_N(j)]. (K20)

Toutes les puissances propres restent présentes, sans mu(j)². Chaque référence individuelle est entre0 et1 ; sa différence est donc de valeur absolue≤1. Le majorant volontairement grossier

    |PP_price|≤2u a sum_(n≤N,properpower) Lambda(n)
              ≤4N^(15/16)u³/log2                    (K21)

vient du nombre de bases≤sqrt N, des exposants≤u/log2 et des poids≤u. Il garde les multiplicités des références au lieu de créer des ressources. K21 est une annotation de raccord alternative du prix raw, **pas un nouveau paiement ajouté au poste B_pp^a déjà acquis**. Le test finite publiera PP_price littéralement avec toutes les bases/exposants.

## 10. Théorèmes Lean concrets à soumettre après sélection

La nouveauté formelle doit importer les définitions effectives18 et dériver, sans axiomatique ad hoc ni sorry :

1. `three_small_primes_face_excludes_physicalMask` : sous trois vrais premiers distincts p_i²≤a et leurs divisibilités à d*b, aucun PhysicalWitness18 ; en particulier l'agrégat canonique est nul sur la face pour chaque paire c,r.
2. `remaining_face_modulus` : P_d=P/gcd(P,d)>1, coprimalité, P|db iff P_d|b, y compris d partageant deux facteurs ; pas de division naturelle tronquée sans divisibilité.
3. `rank_support_and_empty_branch`, `weighted_rank_price_decomposition` : A≤J', J'=0=>A=0 et K4/K5 pour theta_N et rawLambda_N effectifs, toutes références et prix initialement définis sur leurs ensembles réels.
4. `normalized_reference_change_bound` et `large_conductor_unit_price_bound` : K6/K7/K8 avec theta_N≤u, card entiers/floors et les deux primes effectifs de d ; aucune hypothèse de prix déjà petit.
5. `small_unit_modulus_bound` et `small_unit_modulus_multiplicity` : d*k_s≤max(aR,R⁴) et injection fondée sur les facteurs premiers d'exposant1/2, puis au plus40 contributions, borne64 conservatrice pour les trois vrais développements AP.
6. `rank_price_principal_negative` : densités phi/IE effectives, local Euler factor et chi(P_d), K14–K17 ; l'erreur K18 doit être dérivée des erreurs AP définies, pas ajoutée comme axiome de Gamma ou de prix.

Un PASS de ces théorèmes serait un ingrédient arithmétique quantitatif et un estimateur conditionnel de prix. **Il ne remplirait pas la condition de victoire** tant que l'estimation de Gamma_rank et les raccords entiers ne sont pas démontrés. On ne doit pas compiler un simple K4 générique et le nommer bypass.

## 11. Contrat numérique neuf, aucun lancement

Nouvelle tranche N=100000000, x=24000000, 12000000<j≤24000000, alpha100,Q999999,a3163,M1000000,h39,P1771. Ce n'est aucune tranche15–18. Prendre **toutes** les paires c<r de premiers unitaires à N avec d=cr≤3163, même si A_d=0. Les unités N sont exactement l'exclusion2/5. Conserver aussi c3,c7,c11,c13,c23, les conducteurs partageant zéro/un/deux premiers de P, et les unités où h et d se superposent.

Le domaine b entier est

    b_min=ceil(76000000/d),
    b_max=ceil(88000000/d)-1,
    L=b_max-b_min+1, X=d(L-1)+1.

Construire beta complet avec tous s,q physiques, sans sélectionner les candidats j premiers. Les premiers nécessaires aux facteurs images ont une borne indépendante : m<88000000, c≥3, rs>a donnent q=m/(crs)<88000000/(3·3163)<9275 ; s≤a/3<1055. Les premiers≤10000 couvrent donc entièrement cette construction. Pour la primalité des candidats j≤24000000, une liste exhaustive des premiers≤4898 couvre sqrt(j) ; un crible segmenté entier peut être employé, avec justification de complétude. Tous les properpowers sont classés par bases/exposants, pas par absence d'une primalité détectée.

Deux coupes R sont à conserver : R_source=ceil N^(1/32)=2, et R_test=17 comme coupe arithmétique libre pour exercer les branches petit/grand/deux petits. Le second n'est pas annoncé comme le R source. Aucun garde BV/source n'est testé à N1e8.

Le futur producteur, seulement après sélection et autorisation root, doit publier :

- catalogue complet des paires/fibres, supports beta, unités U0/U_s/U/U_s'/U', nombres A,J,J',J_F et P_d ; axes candidats non premiers conservés ; classes P_d effectives ; contrôles K1/K3 pour tous les conducteurs et tous les beta, pas seulement un d choisi ;
- theta entière et raw entier, Gamma_0/Gamma_rank, prix E_unit/L_F/Pi, avec K4 et K20 vérifiés ; chaque composante est séparée pour coefficient log c et pour S(N), et conserve les profils physiques une seule fois ;
- toutes les bases/exposants properpowers et PP_price ; zéro fictif interdit, raw sans mu² ; aucune évaluation de W/D ou nouvelle ressource parent n'est nécessaire à ce contrat ;
- IE réelle pour les unités, P_d, les comptes hors face et les AP T0/T_s/T_F,s ; chaque erreur exacte AP est stockée sur l'intervalle réel, avec X/phi(module) et les primes divisant N retirés ; ces erreurs sont des valeurs finies, pas BV appliqué au banc ;
- registres des modules et de toutes leurs représentations(d,k_s,f), avec preuve de complétude et contrôle du plafond Q_R et de la multiplicité≤40, y compris overlaps3/13 et7/11/23 ;
- K6 vérifié à sa borne sharpened u·A·#lost/#U, K7 avec les +1, branche J'=0/A=0, normalisations et différences de prix aux deux R ; comparaison de Pi avec son principal négatif et les erreurs effectivement mesurées, sans présupposer le signe final ;
- logarithmes par intervalles rationnels sans floats ; les quantités affines en S(N) peuvent être certifiées sur la boîte acquise S(N)=(8/3)C2, 2541/4096≤C2≤11011/16384 pour N1e8, soit S∈[2541/1536,11011/6144]. Cette boîte vient du produit singulier acquis et des facteurs de N ; aucune nouvelle valeur de S gratuite n'est supposée.

Falsificateurs neufs : remplacer P_d par P lorsque d partageP ; rendre Pi nul par simple retrait de la face ; utiliser X=dL sans front ; traiter un module d*k_s comme un produit de facteurs toujours disjoints ; appliquer K18-source avec R_test ou un onsetBV supposé ; oublier PP_price. Si le signe de Pi fini diffère du principal, publier l'erreur réelle qui domine, pas un échec de la dérivation source. Si des prix sont nuls, publier ZERO exact et ne pas inventer un strict signe. L'identité de prix, le niveau et la multiplicité sont les objets à falsifier ; Gamma_rank et D_N restent hors conclusion du banc.

## 12. Portée conservée et obligations restantes

L'estimation nouvelle K18/K19 traite le prix complet de la calibration de rang sur toutes les fibres de l'agrégat canonique. Elle n'assume ni disponibilité de partenaires premiers, ni minoration de Acal, ni petite Gamma. Son signe principal est dérivé de vrais facteurs locaux, ses grandes unités ont un coût de puissance et ses petites unités un niveau AP inférieur à1/2.

Restent ouverts : formalisation complète des gardes source/phi/eta et de K18 ; constantes/onset BV ; Gamma_rank(theta) et ses DD/DM/MD/MM avec le masque semipremier réel ; côté parent C16/C17 et erreurs W ; toutes les familles hors de l'extraction canonique ; union unique des capacités, non-SS/T_A, SS et son gap d'onset ; paiement du ledger entier. Un nouveau signe favorable de prix ne suffit pas à franchir la parité.

Le ledger reste D_N=Bprime^a+Bpp^a+Pband≥2+Zface≥2+Ialpha+2max(e,0). Iglobal acquis, Q/k1, whole U_a incluant r≤alpha, vrais S(bN), principal -S(N)N, c1/b1/e1, longs/faces/nonbulk et P5/K2/J2 entier avant retraits sont inchangés. U4 et variationW ne sont jamais deux paiements. Les1361 archives ne sont pas modifiées.

Statut FINAL conceptuel : estimation de prix dérivée par écrit, candidature pour formalisation et nouveau gate numérique, aucune exécution mathématique de ce rôle, aucun PASS/échec Lean inventé, aucun Win ni NoGo global.
