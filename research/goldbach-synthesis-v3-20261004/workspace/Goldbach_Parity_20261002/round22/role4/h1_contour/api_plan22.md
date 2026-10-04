# ROLE4 — H1/15.3, audit des APIs et premières preuves en source

Statut : SOURCE ONLY. Aucune invocation Lean supplémentaire, aucun calcul
mathématique Python, aucun banc rejoué, aucune installation. Les quatre fichiers
papier ROLE1 gelés ont été lus entièrement ; leur manifeste conserve le SHA
812bad4eb69d612208eae8380d8bdc1dd8ab4fb2605d39eaa790f0479f2b37e3.
La vraie C3/H1 et son interprétation C7/C9 restent ouvertes. Les acquis et le
bilan fixé ne sont pas modifiés. Le seul nouveau résultat auteur compilé de
ROLE4 est Γ3, avec vérification indépendante encore distincte.

## Premiers lemmes réellement dérivés, sans prémisse cible

La première obligation accessible est le raccord Mellin du test fixé
f_Y(x)=(x/Y)exp(-x/Y). `MellinThermal22.lean` construit sa convergence absolue
pour Re(s)>-1 à partir de l'intégrale Γ, transporte celle-ci par x/Y, puis
établit mellin(f_Y)(s)=Y^s Γ(s+1). La duale f_Y(1/x)/x est traitée avec
convergence pour Re(s)<2 et transformée Y^(1-s)Γ(2-s). Douze déclarations
qualifiées sont auditées par des `#print axioms` futurs, sans exécution actuelle.

`MellinThermalInversion22.lean` construit l'intégrabilité verticale sur toute
la droite, en assemblant les deux demi-droites et la réflexion qui préserve la
mesure. Elle applique ensuite le vrai théorème d'inversion du cache sur
-1/2≤c≤3/2, Y≥1, x>0. Aucun `hMellin` ou `hVertical` libre n'entre dans la
conclusion. Les quatre déclarations restent non compilées ; leur dépendance
`GammaContourComponent22.lean` et les modules Γ′/bande élargie restent eux aussi
en source. L'inversion sur toutes les droites c>-1 n'est pas revendiquée ici.

`ZetaEulerDirect22.lean` construit n↦n^(-s) comme homomorphisme, sa convergence
en norme par la vraie p-série, puis relie l'exponentielle des logarithmes des
facteurs premiers à la vraie `riemannZeta`. Cela dérive ζ≠0 pour Re(s)>1.
Les cinq déclarations n'importent pas `LSeries.Dirichlet` et n'appellent pas
la formule vonMangoldt de ce module. La route sélectionnée est exactement
`EulerProduct.exp_tsum_primes_log_eq_tsum` → convergence p-série → somme
analytique de ζ. Cette route utilise la factorisation unique pour le produit
d'Euler, aucun argument de crible ni inversion arithmétique.

Traçabilité honnête : `EulerProduct.Basic` importe `ArithmeticFunction`, fichier
qui contient également des définitions de Möbius et de convolution. Ces objets
ne sont pas employés dans la chaîne de preuves sélectionnée du produit
complètement multiplicatif ; l'import seul n'est pas présenté comme un fichier
sans ces définitions. Le théorème final de série Λ doit toujours être reconstruit
directement, sans la route historique de convolution.

`ZetaReflection22.lean` emploie l'équation fonctionnelle de la vraie ζ dans le
voisinage Re(s)<0, dérive Γ(1-s)≠0, exclut les zéros du cosinus par leur vraie
classification entière, puis obtient ζ≠0 sur -1<Re(s)<0. Le logarithme dérivé
réfléchi est obtenu en différentiant cette identité locale, avec domaines et
dénominateurs payés. Sept déclarations ; pas de nouvelle fonction abstraite
remplaçant ζ, pas de `hTrace`, `hWeil`, zéro arbitraire ou hypothèse RH.

## APIs disponibles et provenance vérifiée

| Obligation | API réelle lue | Portée de lecture et capture |
|---|---|---|
| Transformée et transport positif | `MellinConvergent.cpow_smul`, `comp_mul_left`, `comp_rpow`, `mellin_comp_mul_left`, `mellin_comp_inv` | MellinTransform lignes1–185 TARGETED, 69012e ; SHA183def9a… |
| Inversion de Mellin | `mellin_inversion`, convergence du test + convergence verticale + continuité locale | MellinInversion FULL ea0023 ; SHA38cdb4e7… |
| Intégrale Γ | `GammaIntegral_convergent`, `GammaIntegral_eq_mellin`, `Gamma_eq_integral` | Gamma/Deriv FULL84ccee ; Gamma/Basic lignes78–114 TARGETED f43897 |
| Réflexion de ζ | `riemannZeta_one_sub` avec exclusion des pôles et s≠1 | RiemannZeta FULL a82a8c ; SHA440f0906… |
| Somme réelle de ζ | `zeta_eq_tsum_one_div_nat_cpow`, `summable_nat_rpow_inv` | RiemannZeta FULL a82a8c ; PSeriesComplex FULL8ad96a SHA36558efe… |
| Euler exp-log direct | `exp_tsum_primes_log_eq_tsum` | ExpLog FULL9c5837 SHA d925a62a… ; Basic FULL8e98da SHA715da6e3… |
| Γ non nulle | `Gamma_ne_zero_of_re_pos` | Gamma/Beta lignes425–468 TARGETED62e4ca |
| Cosinus non nul | `cos_ne_zero_iff` et ses zéros (2k+1)π/2 | Trigonometric/Complex lignes1–51 TARGETED62e4ca |
| Quotients dérivés | `HasDerivAt.congr_of_eventuallyEq`, chaîne, produit ; direction new=old vérifiée | Deriv/Basic lignes559–569 TARGETED14b81a ; LogDeriv lignes1–155 TARGETED215702 |
| Réflexion des demi-droites | `MeasurePreserving.integrableOn_comp_preimage`, `measurePreserving_neg` | IntegrableOn lignes219–237 TARGETED11ff80 ; IntegralEqImproper lignes862–887 TARGETEDcee674 |
| Future dérivation de série | `hasDerivAt_tsum_of_isPreconnected` demande un vrai majorant sommable uniforme | SmoothSeries lignes1–102 TARGETED567c8f ; SHA6d9d59c2… |
| Constante γ_E | `Complex.hasDerivAt_Gamma_one`, dérivée réelle et complexe aux entiers | Harmonic/GammaDeriv FULL4dbce0 ; SHAf1d319c9… |

Le paquet de cinq lectures initial 5c0831/… a été tronqué globalement ; ce n'est
pas une lecture FULL de MellinTransform. Les lectures ciblées ou FULL corrigées
ci-dessus seules justifient l'inventaire. Une recherche de déclarations n'est
jamais comptée comme la lecture entière d'un fichier.

## Dettes suivantes et plan de preuves substantif

1. **Euler dérivé direct.** Sur Re(s)≥κ>1, chaque facteur a
   |p^(-s)|≤p^(-κ)≤1/2 et 1-p^(-s) appartient au demi-plan droit.
   Construire sa dérivée -log(p)p^(-s)/(1-p^(-s)), puis le majorant
   2log(p)p^(-κ). Avec δ=(κ-1)/2, log(p)≤p^δ/δ fournit une vraie
   p-série sommable d'exposant (κ+1)/2>1. Employer SmoothSeries sur le
   demi-plan ouvert pour dériver la somme, puis l'exponentielle Euler.
   Développer la géométrique et identifier les puissances d'un unique premier
   avec le Λ direct : convergence double, injection (p,k)↦p^(k+1) et support
   PrimePow doivent être payés. Le théorème du cache
   `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` est rejeté pour cette étape :
   lecture TARGETED5c752b montre explicitement la route convolution.
2. **Suppression du pôle A.** Définir la vraie mise à jour de (s-1)ζ(s) en1
   avec valeur1, à partir de `riemannZeta_residue_one`. Prouver continuité puis
   analyticity amovible, et A(0)=1/2 depuis `riemannZeta_zero`. Cela ne découle
   pas d'une simple définition par update. C7 exige cette vraie analyticité.
3. **ψ et C5.** Définir ψ=Γ′/Γ sur Re(z)>0, dériver sa récurrence depuis
   Γ(z+1)=zΓ(z), puis sa représentation intégrale par une limite effectivement
   dominée d'approximation Γ/Beta. Le cache lu contient les dérivées de Γ et
   les valeurs aux entiers ; aucune API de représentation intégrale complexe
   de ψ n'a été trouvée dans les répertoires Γ/Harmonic recherchés. Cela reste
   une dette, pas une preuve de non-existence universelle d'une telle API.
   Garder les différences e^-u-e^-zu dans un intégrande, prouver le dominateur
   local O(1), celui à l'infini et Fubini. Relier l'intégrale résultante au
   vrai `Arch_Y` par x=exp(v) et les intégrales élémentaires de f/x. Les
   constantes log(4π)+γ_E et le -1 doivent être dérivées exactement.
4. **C4/C3.** Construire l'intégrabilité de G·ζ′/ζ avec les nouveaux
   majorants ; payer l'échange intégrale/série et chaque changement
   d'orientation. Le déplacement du facteur G/(s-1) à travers1 requiert une
   preuve de contour et la décroissance horizontale. Ne pas prendre C4 en
   prémisse de C3.
5. **C6.** L'enveloppe Γ seule est construite en source, mais ne paie aucun
   majorant de F. Dériver série absolue <7 à droite et ψ à gauche, puis intégrer
   les moments exponentiels affines. Le banc ROLE6 à venir doit reprendre
   exactement ces sources ; l'ancien banc Γ21 cas ne valide pas C6.
6. **C7/C9 et évaluateur.** Les restes EM/Stirling, DFT/alias et certificats
   effectifs horizontaux sont des étapes distinctes, encore non exécutées.
   Le théorème des résidus doit porter sur les vrais zéros de A et leur
   multiplicité analytique, non sur une liste externe. Aucune hypothèse de
   non-annulation libre ne remplace le checker effectif du bord.

Précritique ROLE6 reçue sans calcul : garder explicitement le facteur i^k lors
de l'intégration du polynôme sur une cellule verticale ; séparer les budgets
de fonction aux nœuds, positions, poids et accumulation. Pour Stirling, former
logGamma(z)=L32(z+64)-ΣLog(z+j)+reste avant l'exponentielle évite d'employer
l'ancien domaine Re≤16 à exp(logGamma(z+64)), qui peut en sortir. Cette
restructuration numérique ne paie ni les branches, ni les rayons, ni la preuve
uniforme requise ; aucun producteur ou résultat n'est introduit par cet audit.

Ce paquet de 28 déclarations n'est ni PREPARED pour compilation ni PASS.
Il faut encore une lecture indépendante de source, une banque réellement
informative appropriée, le gel des dépendances exactes et une nouvelle gate.
Aucun retour au comptage global abstrait N(t), aucun raccord au coefficient
additif N, aucun paiement de D_N et aucun WIN n'est annoncé.
