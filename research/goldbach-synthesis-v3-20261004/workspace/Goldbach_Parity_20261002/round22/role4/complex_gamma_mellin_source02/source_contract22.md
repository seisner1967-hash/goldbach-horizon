# Mellin–Gamma sur le demi-plan droit — SOURCE02

Statut : SOURCE uniquement, deux modules, 37 déclarations manuelles (27 théorèmes et 10 définitions), 37 impressions qualifiées d’axiomes. Aucun compilateur, probe, parseur de candidat, calcul numérique ou préparation runtime. L’auteur conserve le workpoint SOURCE01 et BORD03. Le principe d’identité utilisé ci-dessous est un théorème analytique général ; il ne remplace pas une identité de trace ζ.

## Objet et conclusion écrite

Pour `w : ℂ`, `Re(w)>0`, `s(t)=2+it`, puissance complexe principale :

`K(w,t)=Gamma(s(t)) w^(-s(t))`,

`F(w)=(1/(2π)) ∫_(t∈ℝ) K(w,t) dt`.

La conclusion écrite est `F(w)=exp(-w)` sur tout le demi-plan droit. Aucun objet Gamma abstrait, aucune prémisse d’intégrabilité, de dérivée, d’analyticité ou d’inversion finale n’est offert. Le premier module contient 22 déclarations reprises byte-identiques du brouillon e54cac5b ; le second paie les 15 nouvelles étapes locales et le prolongement. Ce sont des preuves SOURCE proposées, sans verdict Lean sur ces 37 déclarations.

## Charges construites

`Re(w)>0` place w dans le plan fendu et exclut zéro. Posons b=|Arg(w)|, η=(π/2+b)/2 et δ=η−b>0. La rotation réellement dérivée et indépendamment validée de Gamma, appliquée à +η et −η, et Gamma(2)=1 donnent

`|Gamma(2+it)| ≤ sec²(η) exp(-η|t|)`.

La norme de la vraie puissance principale vaut `|w|^-2 exp(t Arg(w))`. Ainsi

`|K(w,t)| ≤ C(w) exp(-δ|t|)`, avec `C(w)=|w|^-2 sec²(η)`.

La continuité en t et les deux intégrales Laplace réelles de taux δ>0 construisent l’intégrabilité entière. Le transport de la demi-droite négative utilise la mesure de Lebesgue et la négation préservant la mesure, puis Iic/Iio et leur union avec Ioi ; aucune intégrabilité globale n’est supposée.

Pour la dérivation en w, le cpow sur le plan fendu donne réellement

`∂_w K(w,t)=-(2+it) K(w,t)/w`.

Au centre w₀, m=|w₀|/2>0, r=(η+|Arg(w₀)|)/2<η et δ₀=η−r>0. La continuité de Re, de la norme et de Arg sur le plan fendu construit ε>0 tel que, pour z dans la boule de centre w₀/rayon ε,

`Re(z)>0`, `|z|≥m`, `|Arg(z)|≤r`.

La même rotation fixe au centre donne le majorant réel effectif

`|∂_z K(z,t)| ≤ C₀(w₀) (2+|t|) exp(-δ₀|t|)`

avec `C₀=m^-2 sec²(η)/m` ; son intégrabilité est dérivée des moments Laplace a=1 et a=2. La mesurabilité du noyau près du centre, celle de sa dérivée au centre, le majorant uniforme sur cette boule et les vraies dérivées de chaque noyau paient tous les arguments de `hasDerivAt_integral_of_dominated_loc_of_deriv_le` avec μ=volume explicite.

La différentiabilité ainsi construite donne l’analyticité dans le demi-plan ouvert. L’accord sur les réels strictement positifs réutilise exclusivement le résultat Mellin réel indépendamment PASS20. Les réels `1+1/(n+1)` y accumulent en1 ; la préconnexité du demi-plan, déjà dérivée dans GammaPrerequisites22, et le principe d’identité donnent la conclusion écrite, sans hypothèse de prolongement.

## Prix de bord et suite non payée

Le taux fixe δ=(π/2−b)/2 et le taux local δ₀=(π/2−b)/4 s’annulent quand b approche π/2 ; sec²η diverge également. Il n’y a pas d’uniformité gratuite jusqu’à l’axe imaginaire. Sur le papier, le majorant fixe produit la queue `2 C exp(-δH)/δ` pour H≥0 ; la queue de la dérivée est `2 C₀ exp(-δ₀H) ((2+H)/δ₀+1/δ₀²)`. Ces formules de queue ne sont pas de nouvelles conclusions Lean du présent paquet. Il reste à les dériver formellement si elles sont sélectionnées et à payer toute uniformité de bande de phase utilisée ensuite.

L’échange véritable avec Λ, le logarithme dérivé de ζ sur la droite, une formule spectrale uniforme en θ, les erreurs d’une troncature du producteur spectral, la contribution des puissances premières, la frontière canonique et la cible D_N restent ouverts. Une formule Mellin scalaire sur un demi-plan ne paie ni Goldbach ni une annulation de la contribution globale.

## Provenance et lecture

Ordre futur : ComplexGammaMellinLocal22 → ComplexGammaMellinHolomorphy22. Le seul import local antérieur est ThermalGammaMellinInverse22, source daad8b5d/olean e9442776 du vrai batch20, receipt28a07d17 ; sa dépendance GammaPrerequisites22 utilise source9f5e5fe1/oleanfc0dad0b, déjà indépendante. Aucun ancien module n’est recompilé ici. Aucun olean auteur.

Le core copié a été lu FULL830a33 ; nouvelle extension FULLdb9ebf. APIs cache uniquement TARGETED : 4d2864 (dérivation paramétrique, identité analytique, Arg et recherches), 91a1cf (voisinages/ordre/rpow/analyticité et preuve Gamma readonly), 118d87 (moments Laplace, ordre/Arg/cpow), 74755a (norme complexe, div_const et dérivée cpow). Les recherches sur `Analysis/Complex/Norm.lean`, `Data/Complex/Norm.lean`, `Topology/ContinuousFunction` et `Algebra/Order/GroupWithZero/Basic.lean` ont signalé des chemins absents ; ces segments ne sont pas des lectures réussies. Le cache n’est pas lu FULL et aucune fermeture transitive d’imports n’est revendiquée. Le receipt20 a été relu FULLedcabf. Les lectures historiques exactes et les hashes des dépendances sont conservés dans les reçus SOURCE, qui distinguent FULL, TARGETED et BYTE_HASH.

La prochaine revue indépendante et toute compilation nécessitent la sélection séparée du coordinateur. Aucun PASS anticipé, aucun comptage officiel ajouté, aucun WIN.
