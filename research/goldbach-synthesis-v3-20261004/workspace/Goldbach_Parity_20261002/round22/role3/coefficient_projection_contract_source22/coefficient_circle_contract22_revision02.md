# Contrat SOURCE/PAPER du coefficient N sur le cercle — 22

Statut SOURCE_SPECIFICATION_NOT_PREPARED. Aucun nouveau FFT, import, parseur Python, calcul, probe, Lean, builder ou gate. Le seul processus numérique actif reste le banc thermique phase0 lancé sous launch_prepare03 ; il n'évalue pas ce document. Les sources figées sont conservées. Le présent contrôle d'un témoin arithmétique fini est une boussole ; il ne fournit ni une méthode d'estimation par formes bilinéaires ni un contournement de la parité.

## Identité finie exacte et nombre de phases

La source ProjectionIdentity20 désigne ThermalProjectionIdentity22.lean, SHA5b6da908dce97e0ad1ba08a893bd545a4a4c908f969d958102cf9e3509c5e99c, vingt déclarations, lue FULL9a6c51. Son théorème thermalPartialProjection_eq_coefficient construit le projecteur continu à partir de la vraie Λ et démontre sa stabilité pour M≥N, tout a réel. La qualification ici demeure SOURCE tant que le verdict du lot indépendant n'est pas observé. Le noyau défini dans Envelope42 emploie r=e^{-a}, T_{a,M}(θ)=Σ_{n=0}^M Λ(n)r^n e^{inθ}, caractère e^{-iNθ} et normaliseur e^{aN}/(2π). Toutes les puissances premières sont présentes.

Écrire C_N=Σ_{n=0}^N Λ(n)Λ(N-n), avec Λ(0)=Λ(1)=0. Pour K entier positif et θ_j=2πj/K, définir

Q_{a,N,M,K}=e^{aN}/K · Σ_{j=0}^{K-1} T_{a,M}(θ_j)² e^{-iNθ_j}.

Le carré est la corrélation continue écrite T(θ)conj(T(-θ)), car les coefficients sont réels. Ce n'est pas T(θ)conj(T(θ)), qui projette les différences de fréquences.

La somme des caractères vaut1 si K divise m+n-N, sinon0. Elle découle de la somme géométrique d'une racine de l'unité :z^K=1 et z≠1 donnent Σz^j=0 ; le cas z=1 donneK. Pour M≥N, les fréquences m+n-N appartiennent à[-N,2M-N]. Il n'y a donc aucun alias si

K>max(N,2M-N).                                          (A0)

On obtient alors Q_{a,N,M,K}=C_N exactement. Aucun budget de queue de la série infinie n'est nécessaire :le rectangle fini contient déjà toute l'antidiagonale cible. A0 doit être prouvé pour les caractères complexes concrets, puis contrôlé par entiers dans un futur checker, pas accepté comme une heuristique de Nyquist.

Fixer le contrat demandé à N=100000000, M=N, a=1/N, K=N+1=100000001. Alors e^{aN}=e et A0 vaut. Si q_j=exp(2πij/K), on a q_j^{-N}=q_j exactement puisque N=K-1. En posant P(q)=Σ_{n=0}^N Λ(n)e^{-n/N}q^n, le contrôle peut donc utiliser

C_N=e/K · Σ_{j=0}^{K-1} q_j P(q_j)².                    (CIRCLE)

La multiplication par q_j est une identité exacte sur cette grille, pas une approximation du caractère de haute fréquence. Le polynôme qP(q)² est de degré au plus2K-1, sans terme constant :la moyenne des caractères extrait seulement son coefficient de degréK, qui est e^{-1}C_N.

K est impair. Par q_{K-j}=conj(q_j) et coefficients réels, CIRCLE devient

C_N=e/K · [P(1)² + 2Σ_{j=1}^{50000000} Re(q_jP(q_j)²)].  (HALF)

Il faut donc50000001 phases distinctes, dont q_0=1 exact, et50000000 racines complexes. Chaque q_j est construit avec la vraie π dans son enclosure entière. Les exponentielles inθ doivent être réduites par l'indice entier (nj modK)/K, ou par une récurrence prouvée ; un angle flottant réduit sans son incertitude π est interdit.

## Aliases si l'on emploie la trace infinie

Le raccourci T_a infini n'est pas interchangeable avec le témoin fini. Pour K>N, le projecteur discret infini vaut exactement

C_N+Σ_{ell≥1} e^{-a ell K}C_{N+ell K},

tous les termes alias étant positifs. La borne élémentaire Λ(n)≤n donne C_d≤d(d²-1)/6≤d³/6. Avec q=e^{-aK}, l'enveloppe explicite est

E_alias(a,N,K)=1/6 [N³q/(1-q)+3N²Kq/(1-q)²+
  3NK²q(1+q)/(1-q)³+K³q(1+4q+q²)/(1-q)^4].              (ALIAS)

Elle est fermée et continue pour a>0,K>0. L'échange des séries et de la somme finie provient de la convergence absolue déjà majorée. Àa=1/N etK=N+1, q demeure d'ordre e^{-1}, donc cette queue ne donne pas une précision absolue petite. Pour employer un évaluateur spectral de T_a au lieu de P_N, il faut payer ALIAS, ou soustraire le vrai tail T_a-T_{a,N} avec ses primitives et son budget. Aucun passage implicite du banc phase0 à ces50000001 phases n'est permis. La note uniform_phase_contract22 paie une queue Mellin angulaire sur papier, mais sa hauteur H d'ordre NlogN et sa quadrature demeurent des dettes pratiques et formelles.

## Primitives dirigées et enveloppe effective

Choisir une précision de grille fixe S=2^512, EPS=1/S, sans revendiquer qu'un simple flottant possède cette précision. Les constructeurs SOURCE existants dyadic_r01.py fournissent des modèles concrets à recopier/figer dans un futur paquet distinct :

- π par Machin,256 termes pour atan(1/5) et atan(1/239), chaque prochaine queue1/(513*q^513), facteurs16 et4 ; garde3<π<4 et largeur≤128EPS.
- exp128 après division par2^k vers[-1/8,1/8], élargissement2/8^129 avant carrés. Les seuls arguments de chaleur nécessaires sont[-1,0], et le normaliseur est exp(1), dans le domaine concret[-1024,16].
- sin/cos sur le domaine entier de l'argument, réduction d'un nombre entier de tours avec la même boîte π ; garde du réduit[-4,4], polynômes tronqués puis queue2*4^257/256!. Le root q_j n'emploie qu'un angle dans[0,2π] ; le cas q_0=1 est exact.
- log des bases premières par réduction vers[1/2,2], série atanh256 et reste2/(513*3^513)/(1-1/9). Chaque base positive et chaque division a sa garde effective.

Ces formules ont une justification PAPER dans la revue indépendante du paquet thermique ; elles ne sont pas des certificats Lean des primitives de ce futur projecteur. La copie, l'application à tous les nouveaux inputs et leur contrôle indépendant restent à construire. Aucun résultat, boîte, cache ou certificat arithmétique déjà évalué n'est un oracle autorisé.

Un producteur futur doit construire tous les b_n=Λ(n)e^{-n/N}, boîtes réelles dirigées. Soient β_n leurs points de grille et ε_{b,n} leurs rayons effectifs vers le vrai b_n. Pour chaque racine q_j, prendre son point de grille qtilde_j et rayon effectif ε_{q,j} en norme dominée par les deux rayons de coordonnées. Tous ces rayons proviennent des endpoints et des restes construits ; ils ne sont pas des paramètres d'entrée remplaçant une preuve.

Évaluer P par Horner avec points de grille et multiplication complexe dont les deux résidus d'arrondi exacts paient au plus2EPS. L'addition des points de grille est exacte. La norme des queues vraies de Horner est majorée par

A(a)=r/(1-r)², r=e^{-a},

car b_n≥0 et Λ(n)≤n. Si (N+1)ε_{q,j}≤1/2, le binôme paie (1+ε_{q,j})^{N+1}≤2. La récurrence d'erreur

e_m≤ε_{b,m}+(1+ε_{q,j})e_{m+1}+ε_{q,j}A+2EPS

donne le majorant fermé

E_{P,j}=2[Σ_{n=0}^N ε_{b,n}+(N+1)(A ε_{q,j}+2EPS)].       (HORNER)

Il est continu en a>0 et dans les rayons construits. Une récurrence de800 étapes existante ne peut pas être étendue silencieusement à10^8 étapes :la nouvelle preuve HORNER et les gardes de produit/rayon doivent être établies explicitement. Une implémentation en intervalles complets peut aussi utiliser directement ses enclosures effectives si elle évite cette route de points.

Si z_j est le point final de P, c_j=|Re z_j|+|Im z_j|, la norme d'erreur de qP² est au plus

D_j=E_{P,j}(2c_j+E_{P,j})+c_j² ε_{q,j}.                 (PRODUCT)

La norme1 du vrai q est payée par le caractère du cercle. PRODUCT évite de fournir librement une norme de T ; c_j est extrait du point effectivement produit. Les arrondis de l'opération finale qtilde_j z_j² sont ajoutés via leurs certificats, pas oubliés.

Pour la formule HALF, les poids sont1 au nœud0 et2 ailleurs. Le budget du projecteur est e/K fois la somme pondérée des D_j et des arrondis, augmenté du rayon effectif du normaliseur e/K multiplié par une borne effective de la somme numérique, puis du rayon d'accumulation réel. Les additions et multiplications doivent être refoldées à partir d'entiers exacts par un checker indépendant. Aucun EPS libre, rayon absolu fourni en prémisse, norme cible ou accord observé ne crée cette enveloppe.

## Témoin arithmétique, PP et décision falsifiable

Le catalogue futur couvre tous les entiers0..N, sans trous ni doublons. Pour n≥2, un certificat n=p^e*r, p premier, e≥1, r≥1 et p ne divisant pasr classe exactement Λ(n) :r=1 implique logp ; r>1 implique au moins deux bases premières et Λ(n)=0. Le checker doit valider p par une méthode finie exacte indépendante et toutes les factorisations/divisions. n=0,1 sont séparés. Ni probable-prime, ni exclusion des puissances propres, ni simple liste de premiers sans couverture ne suffit.

Le témoin indépendant C_ref est la somme directe finie des poids Λ(n)Λ(N-n), avec logs dirigés et fold entier distinct. Cette somme est uniquement une référence numérique de coefficient ; elle n'est pas une estimation théorique par forme bilinéaire. Tous les PP sont conservés. Une correction optionnelle C_PP est la somme des mêmes termes lorsque l'un au moins des deux entiers est une puissance première propre. C_prime=C_ref-C_PP vaut alors le poids des seules paires premières ; son éventuelle positivité àce N doit être constatée avec des certificats effectifs. Elle ne prouve pas la conjecture pour toutN ni l'inégalité canoniqueD_N.

Le seuil proposé, nouveau et distinct du tau de H1, est τ_projection=1/1000000 dans les unités du coefficient pondéréΛΛ. Un futur résultat informatif exige :catalogue/racines complets ; A0 vérifiée ; boîtes et gardes primitives/prod/HORNER valides ; erreur totale effective du projecteur et de C_ref≤τ_projection ; composante imaginaire compatible avec0 ; différence projecteur−C_ref compatible avec0. Une incompatibilité au-delà des rayons certifiés falsifie l'itération. Une garde de largeur non satisfaite produit NUMERICAL_CONTRACT_INCONCLUSIVE, pas un PASS et pas une réfutation de l'identité. Un accord produit au mieux un auxiliaire numérique au niveau réel de certification des primitives.

Les mutants doivent être propres au coefficient :

1. Mauvaise conjugaison T(θ)conj(T(θ)) remplace l'addition par une différence. Son coefficient CONTINU vaut0 pour M=N, car seule la paire(m=N,n=0) peut contribuer et Λ(0)=0. Mais la même grilleK=N+1 réintroduit alors une alias de différence-1 :sa valeur discrète est e^{aN}Σ_{m=0}^{N-1} b_m b_{m+1}, avec b_m=Λ(m)r^m. Le terme frontière(m=N,n=0) vaut0. Il serait donc faux de déclarer le mutant DISCRET nul. Sa discrimination exige une séparation effective entre cette somme dirigée et C_ref, ou le rejet structurel de la conjugaison/frequence ; aucune séparation ne se présume.
2. Une grille mutante K'=N-4 introduit une vraie alias basse4. Pour M=N et N=10^8, la moyenne devient C_N+e^{aK'}C_4+e^{-aK'}C_{2N-4}^{(M)}, avec C_4=(log2)² et C_{2N-4}^{(M)}≥0. Le défaut est donc au moins e^{aK'}(log2)². La borne log2≥1/2 vient de ∫_1^2 dx/x≥1/2 ; sa discrimination peut être certifiée structurellement par le témoin de fréquence4 et le rejet de A0, sans exécuter une seconde immense grille. Le PASS structurel seul ne certifie pas les primitives du producteur principal.
3. Retirer tous les PP change le coefficient de C_PP ; il faut un témoin PP effectivement nonzero pour exiger une détection. Retirer seulement Λ(4), mutant utile au banc thermique phase0, est NON_DISCRIMINANT ici :N-4=12*8333333 possède les facteurs2et3, donc Λ(N-4)=0 et son terme additif vaut0. Aucune détection fictive de ce mutant n'est un critère de victoire.

## Coûts et dette de faisabilité

Comptes entiers théoriques, sans invocation ni mesure :M=N=100000000 ; catalogue100000001 entiers ; K=100000001 ; phases uniques50000001 ; racines nontriviales50000000. Horner nécessiteN multiplications par racine, soit5000000000000000 produits complexes pour les phases nontriviales, plus les produits finaux et la phase réelle0. Les coefficients requièrent au plusN appels log etN appels exp si l'on ne partage que des valeurs fraîches certifiées. Chaque racine trigonométrique256 ajoute son propre coût. La référence du seul coefficient se calcule enO(N) folds, mais ne remplace pas la projection indépendante.

Une validation par divisions d'essai exhaustives des bases≤N a une borne conservatrice deN floor(sqrtN)=10^12 divisions entières. Des certificats de primalité plus efficaces demandent une source/checker véritable ; aucun gain n'est acquis ici. Un tableau compact de base p enuint32 occupe4(N+1)=400000004B, auquel s'ajoutent puissances/certificats et poids.

La conservation de deux endpoints512bits par coefficient réel exige au moins128(N+1)=12800000128B de payload, hors objets et metadata ; un tableau complet de boîtes complexes exige256K=25600000256B. Cela dépasse la limite d'outputs2GiB du banc thermique actuel ; cette limite ne constitue toutefois pas une information sur la RAM disponible. Un producteur de projection devra donc choisir et certifier une représentation compacte/streaming et son contrat de ressources distinct. Le parcours de toutes les phases en lecture répétée des coefficients garde un coût énorme même si sa mémoire de travail est petite.

Un FFT dirigé pourrait réduire le nombre d'opérations, mais aucun n'est implémenté ou audité dans ces sources. K est ici impair ; un Bluestein standard aurait une convolution power-of-two de longueur au moins2K-1=200000001, doncP=2^28=268435456. Un seul tableau de doubles complexes aurait16P=4294967296B ; un seul tableau de rectangles512bits aurait256P=68719476736B de payload. Il faudrait encore les tableaux auxiliaires, leurs erreurs d'arrondi et des racines certifiées. Un appelFFT flottant ne remplace pas ces preuves. Une autre grille power-of-two pourrait rester sans alias, mais exige davantage de phases et sa propre spécification ; aucun reparamétrage n'est proposé au banc en cours.

Le présent contrat est mathématiquement falsifiable avec toutes ses enveloppes explicites et aucun oracle. Il n'est pas pratiquement PREPARED :manquent le producteur de50000001 phases, la conservation compacte des poids/certificats, la preuve dirigée de sa transformation rapide éventuelle et les validationsLean des nouvelles opérations. Le contrôle exact des aliases ne supprime pas ces charges. H1 uniforme en phase, coefficientN effectivement évalué par ce contrat, suppression certifiéePP, frontière etD_N restent ouverts ; aucune annonceGoldbach/WIN.