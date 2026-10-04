# Droite Re(s)=2 — G2/DOM/queues, SOURCE 01

Trois nouveaux modules, sans compilation ni calcul : PhaseGammaReTwo22 (21 déclarations), PhaseZetaReTwo22 (7), PhaseReTwoTails22 (21), soit49 SOURCE avec49 #print axioms écrits et non exécutés. Le contrat role3/spectral_uniform_phase_source22/uniform_phase_contract22.md SHA7fedc4de0d175fcfdbfdb0d36667e7bf5393c788fa88e3f28bd89c9ef0320306 est lu FULLd70e7a. Les paquets Projection62, sa révision02, phaseGamma51, C5 et toutes banques gelées restent inchangés.

La dépendance GammaPrerequisites22, source indépendante SHA9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7, est seulement lue ; elle n'est pas recompilée. Gamma_rotation_bound fournit la vraie rotation pour Re(s)>0, angle strictement entre−pi/2 etpi/2, construite auparavant via Laplace à taux complexe. L'adjudication batch02 SHA6488a47dfb747394fbb16df8df7282ea660e7016c24e06753a7dad3f50519f02 rapporte23 impressions standards et exit0 pour cette dépendance. La nouvelle lecture3209f7 de cette adjudication est tronquée : scope TARGETED, aucune nouvelle assertion de FULL de tout le document.

Pour s=2+it, prendre beta(t)=atan(t/2). Le vrai domaine atan est prouvé, cos(beta)^(-2)=(t²+4)/4 et Gamma(2)=1 sont évalués. L'inégalité atan(x)≤x pour x≥0 est construite depuis sa vraie dérivée1/(1+x²)≤1 et le théorème des accroissements finis. La relation atan(1/x)=pi/2−atan(x) pour x>0 donne pi|t|/2−t beta(t)≤2 ; t=0 et les deux signes sont traités. Ainsi la SOURCE construit

|Gamma(2+it)|≤(t²+4)/4 · exp(2−pi|t|/2).                 (G2)

La borne de L(t)=−zeta'(2+it)/zeta(2+it) est construite dans un module distinct depuis ZetaEulerLambda22, et non posée en prémisse. Cette chaîne utilise les vrais poids contourLambdaWeight définis par puissances premières, leur borne par log(n), l'identité Euler dérivée et sa convergence absolue. Ses dépendances ZetaEulerDerivative22 SHAfe51d8956fecabaa09063ce31543b91946cc3fae1fd2e3ffadd4fc639be39520 et ZetaEulerLambda22 SHA1a08c2258a3e544b7e9e643de2be9f03bddcff90822592dbbca08c53871d5266 restent SOURCE, sans verdict PASS attribué ici. ZetaEulerDirect22 SHA0d790ed67706e2f3c3556d2c5e7fefd50664177f5fb54584beee1d137e430a71 est le socle déjà jugé selon ROOT ; cela ne valide pas ses deux prolongements.

Pour n≥2, le majorant effectivement dérivé par cette chaîne à Re(s)=2 est2n^(-3/2). Les coefficients0 et1 sont nuls par leur définition première. Le test intégral d'une fonction réellement antitone donne, pour toute somme partielle, Σn≥2 n^(-3/2)≤∫_1^∞x^(-3/2)dx=2 ; le passage à tsum construit la borne4. L'identité réelle zeta'/zeta=−ΣLambdaTerm donne |L(t)|≤4. La continuité du vrai quotient est dérivée de l'analyticité de zeta hors1, de sa vraie non-annulation sur Re(s)>1 et de l'analyticité de sa dérivée, sans fonction abstraite remplaçant zeta.

Pour a>0, theta réel, w=a−i theta, rho=|w|, prendre le pouvoir principal. Re(w)=a paie w≠0 et le domaine de l'argument. La norme exacte rho^(-2)exp(t Arg(w)) est conservée. Poser delta=pi/2−|Arg(w)|>0 ; sa continuité est construite. Le vrai produit défini est

F_w(t)=Gamma(2+it)L(t)w^(-2-it).

G2 et la borne4 donnent

|F_w(t)|≤e²rho^(-2)(t²+4)e^(-delta|t|).                (DOM)

Pour delta>0 et toute hauteur réelleH, la primitive réelle négative

−e^(-delta t)[(t²+4)/delta+2t/delta²+2/delta³]

a pour dérivée (t²+4)e^(-delta t), positive. Sa limite0 à+∞ est construite par les trois moments exp, t exp et t² exp. FTC paie l'intégrabilité et l'intégrale exacte du majorant sur Ioi(H). La continuité des trois vrais facteurs de F et la domination paient ensuite ses deux queues signées sur t>H, pour H≥0. Aucune intégrabilité finale n'est donnée en prémisse.

La somme des deux intégrales signées effectivement définies, multipliée par le vrai coefficient réel1/(2pi) plongé dansC, reçoit le rayon

E(w,H)=e²/(pi rho²)e^(-delta H)[(H²+4)/delta+2H/delta²+2/delta³].

La SOURCE écrit rho^(-2), équivalent à1/rho² sur a>0. Le facteur2 des deux demi-queues et1/(2pi) sont payés dans le théorème de norme ; il n'y a pas d'intégrale cible libre. Ce rayon est conjointement continu en(a,theta,H) sur a>0, même pourH réel. La comparaison aux vraies queues exigeH≥0. Il n'existe aucune borne inférieure constante de delta indépendante de a et theta : les coûts rho^-2 et delta^-1/-2/-3 sont exposés. Aucune hauteur, durée, précision ou feasibilité numérique n'est promise àN=10^8.

La portée fermée de ce paquet SOURCE est G2, la borne4 dépendante de la chaîne Euler SOURCE, DOM, l'intégrabilité et le rayon de la somme de queues signées. L'identité T_a(theta)=(1/(2pi))∫F_w reste entièrement ouverte : inversion de Fourier/Mellin, véritable échange de somme et intégrale, continuation holomorphe du produit sur Re(w)>0, et identification des demi-queues avec la différence intégrale entière/tronquée seront des modules ultérieurs. La périodicité de la représentation spectrale, le majorant uniforme d(a)=atan(a/pi), les enveloppes de quadrature et leur producteur dirigé ne sont pas formalisés ici. Aucune de ces conclusions n'est utilisée comme prémisse.

Statut : SOURCE_ONLY_NOT_PREPARED_NOT_COMPILED. Zéro nouvelle invocation Lean/probe/import Python/calcul numérique/builder/gate par ROLE4 ; pas de fermeture transitive préparée, pas de crédit officiel. PP, frontière canonique, raccord bilantiel D_N et WIN restent ouverts.
