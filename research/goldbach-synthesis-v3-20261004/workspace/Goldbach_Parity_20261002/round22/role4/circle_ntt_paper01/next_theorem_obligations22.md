# Prochain petit contrat de preuve — vrai logarithme puis vraie Lambda

PAPER/SOURCE de spécification, aucun nouveau fichier Lean, compilation ou certification. Cette proposition est autonome du module discret29 de ROLE3. Le contrôleur Python est écrit mais jamais importé/exécuté ; il fournit les opérations exactes à formaliser, pas leur preuve Lean.

## Premier lemme utile sans précision libre

Pour un entier p avec2<=p<=100000000, définir k par2^k<=p<2^(k+1), z=(p-2^k)/(p+2^k), L32=2sum(j<32)z^(2j+1)/(2j+1), et la boîte rationnelle EXACTE décrite par log_box(p,32). Définir A32(p) comme quantized_log_point(p,32), milieu arrondi au plus proche/tiespair/clamp. Énoncé à prouver :

`abs(log(p) - A32(p)/2^58) <= 1/2^58`.

Cet énoncé n'a ni hypothèse de précision, ni epsilon/rayon/égalité finale fourni en entrée. Ses seules hypothèses sont les bornes entières de p ; le point est le résultat mathématique du constructeur rationnel fixe. La primalité n'est même pas nécessaire au lemme de logarithme. Le vérificateur d'endpoints constitue une réalisation exécutable future, pas une prémisse remplaçant ce théorème.

API réelle lue TARGETED612085 :Real.hasSum_log_sub_log_of_abs_lt_one, Log/Deriv.lean284–302. Pour |z|<1 elle donne HasSum(2*(1/(2j+1))*z^(2j+1), log(1+z)-log(1-z)). Réécrire en log((1+z)/(1-z)) sous1±z>0, puis démontrer la queue :pour h>=0,2z^(65+2h)/(65+2h)<=2z^65/65*(z²)^h. La vraie série géométrique converge puisque0<=z²<=1/9<1. Ses termes positifs paient simultanément borne inférieure et reste positif. z=1/3 donne log2 ; addition de k fois cette série et de la série z donne logp. Les mêmes arguments avec81 donnent la boîte40 de vérification.

La largeur32 est <=243/(260*3^65)<2^-96, car3^64>2^96 et243<260. La distance à tout point de la boîte depuis son milieu arrondi est <=2^-59+2^-97<2^-58. Le clamp[0,32] conserve cette borne puisque le vrai logp appartient à cet intervalle. Chaque division ci-dessus a un dénominateur strictement positif ; cet argument doit figurer dans la preuve Lean.

## Deuxième lemme : erreur du coefficient, sans prémisse Lambda-bound libre

Définir mathématiquement qLambda(n)=0 si n=0/1 ou nonPP, sinon A32(minFac n)/2^58. La définition repose sur la vraie IsPrimePow, et garde toutes puissances premières. Le catalogue natif est tenu de prouver qu'il réalise cette définition exacte ; aucune classification extérieure n'est admise gratuitement.

Dériver Lambda(n)<=32 pour n<=10^8 directement de vonMangoldt_apply, minFac_pos/minFac_le, log_le_log/log_pow/log_le_sub_one_of_pos. Les lectures de ces API sont locales et TARGETED ; la preuve ne passe pas par le lemme bibliothèque vonMangoldt_le_log, dont la chaîne n'est pas utilisée ici. Le premier lemme donne ensuite |Lambda(n)-qLambda(n)|<=2^-58 pour les PP, et0 pour les autres. Les bornes0<=Lambda,qLambda<=32 sont construites depuis ces mêmes définitions.

La conclusion proposée est

`abs(sum(n<=N) Lambda(n)*Lambda(N-n) - sum(n<=N) qLambda(n)*qLambda(N-n)) <= (N+1)*(64/S+1/S²)`

pourN=10^8,S=2^58, suivie de la continuité de cette expression fermée surS>0 et de la garde entière2(N+1)(64S+1)*10^6<=S². Les produits utilisent l'identité xy-uv=x(y-v)+v(x-u), le triangle réel et les sommes finies, sans prémisse du majorant final ni identité de projection supposée.

## Charges encore ouvertes

Cette note expose une chaîne de preuve complète sur papier, pas sa traduction Lean achevée. Demeurent à écrire/compiler sous future gate :le pont HasSum→queue positive fermée, les casts rationnels exacts, le round/clamp, la réalisation des points Lambda et la somme finale. Puis la spécification de la transformée DIT/DIF, la primitive racine dans le corps, les invariants native/carries/CRT et le catalogue Lucas. Le contrôleur ne réalise pas ces preuves par son simple accord numérique. Aucun coefN positif, PP retiré, frontière ouD_N n'est conclu.
