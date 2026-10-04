# CIRCLE — route entière rapide, contrat PAPER distinct

ROLE2 temporaire. Statut PAPER_ALGORITHM_SPECIFICATION_NOT_PREPARED, ni producteur disponible ni certification indépendante. Aucun calcul, import, probe, FFT, compiler, builder ou gate. Les paquets Re2, Identity03 et tous anciens bancs restent immuables. Priorité toute nouvelle erreur réellement observée sur Identity13. Les deux drafts antérieurs89abd29…/9809d808… restent conservés ; ce document final distinct corrige leur spécification de référence indépendante et ferme la description des contrôleurs sans les exécuter.

Sources lues FULL : coefficient_circle_contract22_revision02.md (SHA9e6d349ff283b1914750c05473d50982795a641cf6b429369504fc7b9ef73ddf, fdddd9), revue indépendante coefficient_circle_paper_review22.md (SHAbd4161cc33953e41c401631a3d92d8c9480f9cbdb035b86507ff7eb4bc01b6d9, ee35d8). Leur contrat K=N+1/a=1/N et leurs artefacts ne sont pas modifiés.

## Nouvelle grille et objet exact

N=100000000, M=N, K=2^27=134217728. Choisir a=0 seulement pour le polynôme FINI : P(theta)=sum(n=0..N) Lambda(n) exp(i*n*theta). La trace infinie T_0 n'est pas invoquée, car sa convergence n'est pas construite. Les identités finies autorisent tout a réel. Pendant la clôture PAPER, Identity20 révision03 a obtenu un vrai PASS20 indépendant (lot13, source8bb1eb…, oleaneb0d3ff…, START16:20:01.870006→FIN16:20:26.174953UTC, reçu9ce9bdf…, log1fac91…, tous deux lus FULL3957bd). Elle prouve la projection CONTINUE ; le nouveau transfert discret/NTT reste PAPER et son futur verdict n'est pas anticipé. Aucun ancien module n'est recompilé ou importé par l'auteur. Poser C_N=sum(n=0..N) Lambda(n)Lambda(N-n), toutes puissances premières conservées.

Les fréquences m+n-N sont dans[-N,N]. K>N les rend non multiples deK sauf fréquence0. Ainsi la projection continue de P(theta)^2 par exp(-iNtheta) égale la moyenne sur les K racines complexes, puis le coefficientN. Cette orthogonalité discrète doit encore être formellement reliée aux caractères concrets. Aucun q_j complexe n'est approché dans l'algorithme ci-dessous :on calcule le même coefficient d'un polynôme rationnel par homomorphismes de corps finis. Ce transfert algébrique est une charge de preuve ; il n'évalue ni la zeta uniforme en phase ni une trace spectrale nouvelle.

## Logarithmes construits, pas précision libre

S=2^58. Pour chaque base première p réellement certifiée, choisir k entier avec 2^k<=p<2^(k+1). p<=N<2^27 donne0<=k<=26. u=p/2^k, z=(p-2^k)/(p+2^k), donc0<=z<1/3. Définir rationnellement, sans transcendantale native,

L_m(z)=2 sum(j=0..m-1) z^(2j+1)/(2j+1),
R_m=2/( (2m+1)*3^(2m+1)*(1-1/9)).

Le développement exact de log((1+z)/(1-z)) et sa queue positive donnent log p dans
[k*L_m(1/3)+L_m(z), k*L_m(1/3)+L_m(z)+(k+1)*R_m].
Les divisions sont des divisions d'entiers exactes, avec dénominateurs strictement positifs ; aucune bibliothèque log/float n'est utilisée.

Le producteur proposé prend m=32. Sa largeur est au plus27*R_32=243/(260*3^65)<2^-96 :3^64>2^96 et243<260. Le point A_p/S est l'arrondi au plus proche du milieu rationnel, ties vers l'entier pair, puis clamp à[0,32]. Le clamp ne peut augmenter la distance à un vrai poids de cet intervalle. Les deux distances aux endpoints sont recalculées par entiers ; la garde impose toutes deux <=1/S. Le reste fermé et l'erreur d'arrondi donnent déjà une marge :1/(2S)+2^-97<1/S. Ce calcul n'a pas été exécuté ici.

Pour le checker indépendant, m=40 produit une NOUVELLE boîte exacte ; il vérifie la distance du point stocké à ses deux endpoints <=1/S, au lieu d'accepter le rayon annoncé. Après vérification des transformées et fold des mêmes points A, il reconstruit aussi ses propres points B_p/S par le milieu de cette boîte40 et la même règle d'arrondi/clamp. Le fold de B est une référence numérique indépendante des points A, avec son propre rayon. Ce n'est pas un oracle ni une référence flottante. La formule de série/reste et les entiers de l'implémentation native restent à auditer/formaliser ; leur application effective à tous les p reste OPEN.

La source fixed_parameter_log_model22.py écrit réellement les tests des constantes et le constructeur des boîtes/points par entiers. Elle n'est ni importée ni exécutée ici. Ses fonctions ne prennent aucun rayon de log en entrée. Ce modèle unique partage ses routines32/40 :il est une spécification logique, pas deux implémentations indépendantes. Le futur checker natif devra reconstruire log40 dans sa propre source et ne pourra importer le producteur pour se déclarer indépendant. Les endpoints ont un dénominateur commun :si la borne inférieure estn/d et la largeur estw/v, retourner(n*v,n*v+w*d,d*v). Le milieu et les gardes se calculent alors avec ce même dénominateur, évitant la croissance d'une addition naïve de fractions déjà apparentées. La source conserve explicitement le reste positif avant de quantifier.

La borne vraie Lambda(n)<=32 pour0<=n<=N suit directement de sa définition :Lambda(0)=Lambda(1)=0 ; sinon Lambda(n) vaut log(minFac n) ou0, minFac n<=n ; log n<=log(2^32)=32log2<=32, avec log2<=2-1. Cette route n'utilise ni inversion arithmétique ni estimation de progressions. Le point quantifié est0 si n n'est pas une puissance première, et A_p sinon. Écrire A_n, y_n=A_n/S et0<=y_n<=32. La classification doit être certifiée sur tous les n, pas importée d'une liste de premiers.

## Enveloppe réelle et comparaison falsifiable

Pour x_n=Lambda(n), |x_n-y_n|<=epsilon=1/S est une conséquence de la classification/logarithme ci-dessus, pas une prémisse finale libre. L'identité xy-uv=x(y-v)+v(x-u), avec0<=x,v<=32, donne |x_n*x_(N-n)-y_n*y_(N-n)|<=64epsilon. Un majorant légèrement plus large, valable aussi si le clamp n'est pas employé et |y|<=32+epsilon, est

E_log(N,S)=(N+1)*(64/S+1/S^2).                         (E)

Donc |C_N-c_N/S^2|<=E_log, où c_N=sum A_n*A_(N-n) est ENTIER. E_log est fermé et continu en S>0 (et dans B si64 est remplacé par2B). À ce S fixé, 2E_log<10^-6 se vérifie uniquement par multiplication d'entiers après suppression de S^2 :cette vérification effective reste obligatoire. Aucun epsilon fourni par un utilisateur ne remplace les endpoints reconstruits.

Les quatre budgets sont explicites :logarithmes E_log dérivés sur papier ; alias0 sousK>N/M=N ; transformation/CRT0 sous les gardes exactes ; accumulation0 sous bornes de mots et arithmétique entière vérifiées. AUCUNE de ces gardes n'est déjà vérifiée sur un output de ce contrat. Il n'existe pas de budget de troncature infinie. La référence c_B/S² recalculant indépendamment les points de log avec m=40 reçoit sa propre enveloppe du même type. |c_A-c_B|/S²<=2E_log est la garde réelle, tandis que le fold direct des MÊMES points A doit égaler EXACTEMENTc_A CRT. La première paie les vrais poids, la seconde contrôle l'algorithme entier ; aucun accord de points ne remplace la preuve analytique des restes.

Le résultat numérique falsifiable impose :couverture/classification/primalités/logs, toutes gardes modulaires, même c_A CRT et fold A direct indépendants, |c_A-c_B|<=2(N+1)(64S+1), 2(N+1)(64S+1)*1000000<=S², et aucun dépassement de ressources. Ces deux gardes ont supprimé les divisions/epsilon libre. Une différence d'entiers CRT/fold A après vérifications exactes falsifie la réalisation algorithmique. Une incompatibilité avec le fold B au-delà des rayons construits falsifie une réalisation/primitive sous les obligations analytiques payées ; elle ne réfute pas Goldbach. Un log trop large donne NUMERICAL_CONTRACT_INCONCLUSIVE. Un temps/mémoire dépassé donne RESOURCE_LIMIT_NO_VERDICT. Un échec de primalité/racine donne INVALID_MODULAR_PARAMETER ; aucune conclusion de parité.

La mauvaise conjugaison est rejetée structurellement :elle encode une différence, et sur cette grille des différences peuvent aliaser àN-K. Une séparation numérique d'avec C_N n'est pas présumée. K'=N-4 garde le témoin d'alias bas4 du contrat original, mais n'est pas une taille admissible radix2 de ce contrat. Lambda(4) retirée seule reste non discriminante àN. Tous les PP sont conservés ; toute mutation PP exige son vrai témoin effectif.

## Cinq paramètres modulaires concrets à vérifier

La table suivante contient des CANDIDATS fixes, pas des primalités ou ordres déjà certifiés. La future source doit vérifier les cinq lignes AVANT toute transformée, sans recherche ou substitution silencieuse.

| p | c avecp=cK+1 | g | omega défini par entier |
|---:|---:|---:|---|
|2013265921|15|31|31^15 modp|
|2281701377|17|3|3^17 modp|
|3221225473|24|5|5^24 modp|
|3489660929|26|3|3^26 modp|
|3892314113|29|3|3^29 modp|

Checker écrit :fixed_parameter_log_model22.py/check_fixed_constants. Vérifier entiers distincts et impairs, p=cK+1, p<2^32, primalité par TOUTES divisions2<=d<=floor(sqrt p), puis omega calculé par powmod entier, omega^K=1 etomega^(K/2)!=1 modp. La borne65535 couvre les diviseurs nécessaires pour p<2^32 ; au plus5*65534 divisions pour ce contrôle. Pour K puissance de2, les deux tests d'ordre donnent ordreK dans le vrai corps si la primalité a été vérifiée. Les omega inverses etK^-1 sont reconstruits par Euclide, puis produit avec leur argument vérifié=1. Les valeurs exactes de omega sont définies par les expressions de la table, pas choisies dans un output libre. Si une candidate échoue, le contrat est INVALID, aucune nouvelle modulus choisie implicitement. Le contrôleur SOURCE est instancié ; résultats effectifs de primalité/ordre/inverses/tau sont tous OPEN puisque aucun test n'a été exécuté.

## Transformation exacte et CRT

Sur chaque p, transformer A_0..A_N complétés par0 jusqu'àK. Le DFT algébrique est F_j=sum A_n omega^(jn) modp. Les butterflies radix2 ci-jointes construisent exactement ce DFT si ses invariants sont prouvés ; aucun appel FFT/float. Le résidu cible vaut

r_p=K^-1 sum(j=0..K-1) F_j^2 omega^(-Nj) modp.

L'orthogonalité dans le corps donne la somme des coefficients aux niveaux congrus àN. Le degré<=2N etK>N imposent seul niveauN. La formulation évite une transformée inverse entière :une réduction pondérée unique donne ce résidu. Cette réduction doit réellement parcourirK entrées.

0<=A_n<=32S=2^63, donc0<=c_N<2^153 carN+1<2^27. Le produitPi des cinq p est>2^154 :le premier dépasse2^30, les quatre autres2^31. CRT fournit UN entier c dans[0,Pi), vérifie tous ses résidus et imposec<2^153. L'unicité sous cette borne rendc=c_N. Toute division/Euclide/borne intermédiaire du code devra être contrôlée ; aucune reconstruction à signe ou arrondi.

Les résidus sont uint32 ; additions/soustractions emploient uint64 avant réduction ; products de deux résidus<p<2^32 sont<2^64. La réduction finale fait total+product<=p(p-1)<2^64 avant réduction. Les points A_n/B_n sont uint64 ; leur produit est uint128 et leurs folds uint192 sous borne2^153. CRT emploie un format entier explicite au moins192bits, ou des membres uint64 avec carries vérifiés ; ses products auxiliaires doivent être bornés/implémentés sans overflow.

Les logarithmes emploient un format multiprécision borné, pas les floats. Pour32termes, H<64^32=2^192 etD^63H<2^1956 ; pour log2, dénominateur3^63H<2^318. Leur combinaison avant la queue a dénominateur<2^2274 ; la queue uniforme possède dénominateur4*65*3^65<2^139, donc dénominateur de boîte<2^2413. Numérateurs, midpoint, multiplication parS et distances ajoutent moins de128bits :4096bits suffisent POUR LA FORMULE AU DÉNOMINATEUR COMMUN ÉCRITE. Pour40termes, H<128^40=2^280, D^79H<2^2492, 3^79H<2^438 ; boîte après la queue<2^(2930+171)=2^3101 ; mêmes opérations ajoutent moins de128bits, donc8192bits est une garde conservatrice. Le modèle SOURCE vérifie bit_length à chaque résultat intermédiaire ; une future implémentation native doit implémenter ces products exactement et vérifier sa mémoire de travail. Ces comptes symboliques ne certifient pas encore le code natif.

## Catalogue exact, source et checker manquants

Un fichier dense f(n), uint32 sur0..N, fournit pour chaque n>=2 un facteur premier candidat f(n) divisantn, avec2<=f(n)<=n. Tous les n sont parcourus une fois, sans trous/doublons. Pour f(n)<n, la primalité de cette base est déjà vérifiée à un indice précédent. Pour f(n)=n, un témoin Lucas g_n est nécessaire :la factorisation complète de n-1 est extraite par divisions répétées utilisant les f(r), r<n ; chaque base y est alors déjà certifiée. Vérifier g_n^(n-1)=1 modn etg_n^((n-1)/q)!=1 pour toute base première distincte de cette factorisation. Le vrai critère Lucas est présent dans le cache, sa source est lue ; aucune nouvelle certificate n'est produite aujourd'hui. Extraire la valuation de f(n) dansn classe exactement les PP par résidu final1 ; le résidu>1 donneLambda(n)=0. Les cas0/1 sont séparés.

Le producteur de ce fichier et des témoins reste OPEN. Une fallback déterministe de divisions d'essai a une borne conservatriceN*floor(sqrt N)=10^12 divisions ; elle ne constitue aucune promesse pratique. La génération des témoins Lucas n'a ni algorithme performant implémenté ni coût mesuré. Aucune liste de premiers préparée ou probable-prime n'est acceptée.

Le checker DOIT reconstruire les cinq transformées exactes à partir des points A/classifications vérifiés, par une implémentation indépendante DIF (producteur DIT). Un hash des tableaux ou une poignée d'évaluations aléatoires ne certifie pas tous les butterflies. Ne conserver que les résidus finaux suffit aux outputs si le checker refait réellement le travail. Il fold A avant de réutiliser le tableau des points pour construire B et fold B. Il peut donc recalculer la boîte40 deux fois par base première, une fois pour vérifier A et une fois pour quantifier B, sans augmenter le payload simultané. Ce coût supplémentaire doit être compté ; la structure seule ne valide ni les logs ni la réalisation native.

## Ressources explicites, pas délai garanti

PourK=2^27,27 étages donnentB=K*27/2=1811939328 butterflies par modulus. Une multiplication de donnée par twiddle et une avance de twiddle coûtent au plus2B products modulaires ; la réduction finale au plus3K. Sur cinq moduli, le producteur coûte au plus20132659200 products modulaires, plus additions/permutations/Euclide/certificats. Le checker indépendant coûte un ordre identique, soit au plus40265318400 products pour les DEUX réalisations, avant catalogue/logs/référence. Le producteur appelle le log32 au plus une fois par base, le checker le log40 au plus deux fois par base sous la politique de réutilisation mémoire ci-dessus, soit au plus32P et80P termes rationnels, P<=50000001. Les deux folds coûtent2(N+1) products128bits plus leurs additions192bits. Vérifier chaque certificat Lucas demande jusqu'à27 bases distinctes de n-1 et des exponentiations d'au plus27bits, sans coût de génération garanti. C'est un compte symbolique de l'algorithme, aucune mesure native, aucune affirmation de fin sous3600s. La génération/verif du catalogue peut dominer.

Une seule modulus est active à la fois. Tableau NTT uint32 :4K=536870912B. Points d'entrée uint64 :8(N+1)=800000008B. Catalogue denseuint32 :400000004B. Leur payload simultané est1736870924B ; réserve de travail proposée128MiB, soit1871088652B de buffers explicitement alloués. Ce n'est pas une mesure de RAM disponible, et le runtime/OS/cache de fichiers doivent être comptabilisés séparément. Allocation impossible=>RESOURCE_LIMIT_NO_VERDICT.

Outputs :catalogue400000004B ; records triés (p,g,A_p),16B chacun. Il y a au plusN/2+1 bases premières par l'argument élémentaire de parité, donc au plus800000016B. Total payload1200000020B, plus headers/manifest/logs plafonnés8MiB. Aucun tableauNTT complet ni certificat de chaque butterfly n'est exporté. Le checker recalcule, sans prétendre qu'un export condensé prouve la transformée. Si un fichier de points dense supplémentaire est écrit, ses800000008B sont ajoutés explicitement, total2000000028B avantheaders/logs ; sa compatibilité avec2GiB doit être vérifiée. Ce contrat définit des payloads, pas un launcher ni des limites ROOT nouvelles.

## Verdict de faisabilité et prochain bloc utile

Route de TRANSFORMATION spécifiée par opérations entières détaillées, erreur réelle fermée dérivée sur papier, aucune FFT non certifiée. Route end-to-end NON_PREPARED :les cinq premières vérifications modulaires ne sont pas exécutées ; producteur/checker natifs et preuves de leurs invariants absents ; catalogue exact/témoins/logs non produits ; disponibilité mémoire et temps inconnus. Aucun compilateur C/C++/Rust, bibliothèque native128/192/4096bits ou noyau NTT présent n'a été inspecté, probé ou installé :leur disponibilité est OPEN. Le modèle Python écrit est un contrôleur logique des constantes/logs, pas un noyau performant de134millions d'entrées. On ne peut actuellement annoncer un banc N=10^8 réalisable dans les ressources du banc thermique. Le passage de5*10^15 products complexes Horner à ces comptes modulaires ne ferme pas ces dettes.

Prochain petit théorème SOURCE utile, distinct du module discret29 de ROLE3 :dériver directement Lambda(n)<=32 pour n<=10^8 depuis minFac et log, puis prouver par triangle et somme finie |C_N-c_N/S^2|<=(N+1)(64/S+1/S^2) depuis les enclosures de logs définies, et la continuitéS>0. Ensuite payer la spécification DFT radix2/orthogonalitéCRT, avant un futur paquet native SOURCE et sa revue indépendante. Ces théorèmes ne sont pas présents ici comme résultats compilés.

Le témoin calcule seulement un coefficient de corrélation fini avec toutes les PP. Il n'absorbe pas la parité, n'apporte aucune positivité universelle, aucune suppressionPP ni minoration de frontière et aucune cibleD_N. H1uniforme/Goldbach/WIN demeurent ouverts.
