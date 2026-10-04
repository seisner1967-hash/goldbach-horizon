# Addendum distinct de domaines — aucune modification des contrats anciens

La continuité des expressions fermées sur leurs domaines positifs ne prouve
pas leurs inégalités sur tout ce domaine. Pour les majorants W, Warch et C8,
la preuve décrite utilise Y≥1. Le domaine Y>0 suffit seulement à la
continuité. Le banc fixe Y=10000 et respecte Y≥1.

Les queues arithmétiques emploient X,Q entiers ≥2. La queue primale exige
en outre X/Y≥1+1/logX. Alors x*log(x)*exp(-x/Y)/Y décroît pour x≥X :
x/Y-1-1/logx est croissant. La somme n>X est donc majorée par son intégrale.
Deux intégrations par parties et 1/x≤1/X donnent même

    exp(-X/Y)*[(X+Y)logX+Y+Y²/X].

La formule contractuelle avec 2Y²/X est conservatrice. À X=1000000,
Y=10000, la condition est satisfaite : X/Y=100 et logX>1.

Pour Q≥2, log(x)/x² décroît pour x≥Q. Avec Lambda(n)≤logn et exp(-1/(Yn))≤1,
la comparaison intégrale donne (logQ+1)/(YQ). Les deux queues sont positives.

Pour R≥2, x-x⁻¹≥3x/4 sur x≥R. L'inégalité triangulaire et les trois
intégrales positives donnent la queue signée Arch de rayon

    (4/3)*[exp(-R/Y)+1/(2YR²)+2/(YR)].

Les substitutions numériques constantes nécessitent pi>3,
exp(-1)<3/8 et log(1000000)<16. La dernière inégalité suit de
exp(2)>7, donc exp(16)>7⁸=5764801>1000000. Ces faits papier peuvent être
certifiés séparément ; ils ne sont pas des observations du résidu.

La quadrature Arch16Warch est une spécialisation à R=1000000 avec logR<16.
Elle ne remplace pas la vraie longueur logR ni la largeur logR/128.
La source transporte leur incertitude dans les positions ET les poids.
La borne du mutant primal4 supérieure à1/Y est propre aux paramètres fixés
(notamment Y=10000>8), pas une assertion pour toute la famille Y≥1.

EM : pour couvrir le disque de Cauchy1/16 de toute la garde source
[-7/8,2]+i[-401/4,401/4], le même reste se prouve sur
[-1,3]+i[-101,101]. Tous les facteurs s+j, j≤127, y ont norme<230,
sigma+127≥126 et128^(1-sigma)≤128². Le papier initial utilisait [-1,2]
pour les nœuds effectivement visités ; ceux-ci, élargis de1/16, restent
déjà dans [-1,2]. L'élargissement à3 ci-dessus couvre aussi l'API générique
sans changer la formule, les constantes, les sources ou les paramètres.

Gamma/Stirling : les points visités satisfont1/4≤Re z≤3. Après shift64,
le disque1/16 a Re w≥64+3/16>64 ; le reste périodique est uniforme en Im w.
Les divisions et gardes sont ensuite contrôlées sur les boîtes produites.

Les continuités et inégalités familiales nécessitent leurs preuves Lean
distinctes. Cet addendum est SOURCE/PAPIER, pas un nouvel axiome, run ou PASS.
