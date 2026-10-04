# Charges de preuve — futur formaliseur, pas de fichier Lean ici

La theorem finale doit porter sur les VRAIS objets Gamma,zeta,Lambda et
les intégrales réelles/complexes C1–C5. Interdire sorry, axiome analytique
nouveau, cible en prémisse, liste arbitraire de nombres appelés «zéros»,
borne d'erreur libre ou résultat numérique promu en identité universelle.

Ordre suggéré :

1. Domaine Mellin de f_Y, intégrale Gamma et inversion pour -1<Re(s),
   avec intégrabilité et Fubini justifiés. Importer uniquement des acquis
   compilés réellement pertinents ; les auxiliaires Epstein sont distincts.
2. Logarithme dérivé Euler sur Re(s)>1 à partir de convergence absolue du
   produit et différentiation locale. Preuve directe de Lambda et Lambda<=log,
   sans dépendance à la convolution Möbius historique de mathlib.
3. Vraie équation fonctionnelle de zeta et dérivation de chi ; récurrence de
   psi et sa représentation intégrale sur Re(z)>0. Gamma non nulle et zeta
   non nulle sur les deux droites ; suppression d'A en1, valeurA(0)=1/2.
4. Calcul C4 puis C5 avec transformations d'orientation, u=2v et x=exp(v).
   Ne jamais scinder en intégrales divergentes les différences près deu=0.
   Construire un dominateur local O(1) et un dominateur à l'infini ; la
   valeur amovible Arch(1)=f1/2 doit être un lemme dérivé.
5. C3 intégrale globale et C6 : utiliser H2 réellement prouvée, les deux
   récurrences Gamma, la série psi et les intégrales exponentielles exactes.
   Aucun N(t), RH ou théorème de compte des zéros nécessaire à C3/C6.
6. Euler–Maclaurin pair à reste et Stirling à reste périodique ; la norme
   Bernoulli et la majoration du produit fini sont preuves générales, les
   comparaisons rationnelles de paramètres sont vérifiées ensuite.
7. Quadrature de fonction holomorphe : coefficients par Cauchy, alias DFT,
   reste géométrique et intégrale exacte du polynôme. Un fichier général
   avec holomorphie en prémisse peut être auxiliaire, mais la finale doit
   dériver celle de nos deux vrais intégrandes et leur majorant ferméW.
8. Cellules horizontales : un checker de certificats vérifie toutes les
   enclosures et couverture finie. Le théorème final peut recevoir les
   certificats concrets contrôlés, pas une hypothèse «zeta sans zéro au bord».
   Résidu pondéré avec multiplicité de zéro analytique fournit C7/C9.

Débts analytiques (universels) : étapes1–7 et résidus ; aucun déjà formalisé
par les fichiers papier. Certificats numériques (effectifs) : nouveaux nœuds,
couverture des512cellules, constantes, arithmétique Lambda jusqu'aux coupures,
enclosures, accumulation et mutations. Une garde de largeur échouée indique
UNRESOLVED ; elle ne devient pas un axiome. Exécutions nécessaires : au moins
une nouvelle source figée et compilations enregistrées par le Juge indépendant.

Le coût204800nœuds n'est pas garanti praticable avant précritique. Le budget
sharp de FINAL1/FINAL2 reste non informatif/coûteux ; le présent contrat ne
demande pas son exécution. Aucune charge générale équivalente àGoldbach ou
àD_N n'est mise en hypothèse.

Raccord additive encore absent : il faut un signal global complexe uniforme
sur le vrai contour additif, sa corrélation avec tous les termes de puissances
propres, une extraction àN sans alias cachés et un contrôle favorable réel.
Puis relier aux poids physiques/modèles et à chaque charge du bilan fixé
B_prime^a+B_pp^a+P_band_ge2+Z_face_ge2+I_alpha+2max(e,0), fronts, unités,
k=1,Q et wholeU_a. Une identité thermique exacte n'obtient aucun de ces
paiements par simple analyticity ou unitarité. Le seuil logN>=10^24 reste
acquis et ne s'applique pas au bancN=1e8. Pas de WIN.
