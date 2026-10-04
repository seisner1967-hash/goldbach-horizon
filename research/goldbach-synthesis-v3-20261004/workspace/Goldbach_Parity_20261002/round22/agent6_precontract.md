# ROLE6 — précontrat continu22 et premier banc auxiliaire préparé

Le premier banc praticable proposé est le déroulement réel d'Epstein à s=3/2. Sa source ferme l'arrondi, les endpoints, la queue et un contre-test de recouvrement. Il n'a pas été exécuté. Les deux propositions globales conservent une identité papier cohérente mais n'ont pas encore un résultat numérique ou Lean : l'isolement compact de Weil a une enveloppe actuellement non informative, et l'extraction par diffusion demande un nombre astronomique d'évaluations. Les annexes lissées de Weil et de chaleur constituent des étapes suivantes distinctes.

| Couche | Identité exacte sur papier | Majorant fermé | Faisabilité à N=100000000 | État réel / obligations |
|---|---|---|---|---|
| Weil compact K_N, coefficient additif | Normalisation et deux applications cohérentes ; convergence à formaliser | Oui, normes construites et queue sans RH | NON_INFORMATIVE_BOUND avec normes actuelles ; pas identité fausse | Aucun calcul / aucune preuve Lean ; données complètes de zéros et pont D_N ouverts |
| Diffusion modulaire, coefficient additif | Epstein et signe D=L−L_shift cohérents ; vraie diffusion exige résolvante/unicité | Mellin, Poisson, deux alias et propagation explicités | Contrat proposé astronomique ; évaluations complexes certifiées absentes | Aucun calcul / aucune preuve Lean ; évaluation et géométrie ouvertes |
| Annexe réelle Weil H_Y | Modes0/1, dual, archimédien et puissances conservés | Queues exponentielle/rationnelles cohérentes | Plausible à Y=10000,T=100, sous certification de tous zéros et intégrales | Précontractuelle ; pas producer READY sans ces certificats |
| Annexe réelle chaleur F(t_ann) | Signal Λ exact et différence K explicite | Poisson-Mellin + queue raw1..N explicites |8193nœuds, K64, référence entière1..N ; arithmétique complexe à construire | Précontractuelle ; pas HEAT_AUX_PASS actuel |
| Déroulement Epstein s=3/2 | Primitive, q-recouvrement, signe m et télescope vérifiés sur papier | Queue positive et arithmétique dyadique neuve fermées en source |18cas de base +6cas y=√N ; ressources modestes avec compression annoncée | PREPARED_SOURCE_ONLY ; passage Lean, mode0 et vraie diffusion restent distincts |

## 1. Directive, acquisitions et périmètre

Le pivot définitif est celui de `round22/USER_DIRECTIVE.md` (SHA c5aa8310ad54c57726339a8e99057f158254eb6d113ac3aeb71ddc9627f23947) et `PROBE_BLOCK.md` (a896c9d0fa4114845b20c3023246dcb987463923df798cac2c537c70cfb73fc3), lus FULL. Il autorise la corrélation spectrale continue et la géométrie indépendante des premiers. Les formes bilinéaires arithmétiques, crible combinatoire, inversion de Möbius, décompositions Vaughan et estimations scalaires de restes AP sont abandonnés pour le nouveau travail. Ni les archives, ni les notations et acquis ne sont remis en cause.

ROLE6 a réalisé0banc mathématique21 et0compilation21. Les sept sources AP21 partielles n'ont jamais été lancées ; elles sont maintenant archivées et inchangées. L'unique conservation21 réelle (START2026-10-03T05:18:32.248223UTC, fin05:18:40.795646UTC, exit0) était metadata-only ; elle est distincte de toute vérification mathématique. Le registre22 contient3089archives protégées, SHA875cebdd8e510fe3341b05009a76991801777b2a060a07229c5323033226ba99 ; sa création/lecture metadata par root n'est pas une invocationROLE6. L'ACK détaillé est `role6/pivot_ack22.json`.

À la préparation de ce rapport :0nouveau calcul mathématique22,0import de bibliothèque mathématique,0probe API numérique,0compilation,0préflight conservation22. Les fichiers neufs sont écrits exclusivement sous `round22/role6` et le présent rapport ; aucun ancien producteur, résultat, log, kernel, PASS ou signe n'est rejoué. Le seuil source u=logN≥10^24 est conservé ; le test fini N=10^8 n'y appartient pas.

## 2. Weil : normalisation exacte et coût du coefficientN

Pour support strictement supérieur à1, la formule complète spécialisée donne μ_Λ(f)=∫f a−ΣρM_f(ρ), avec a(x)=1−1/[x(x²−1)]. Le pôle1, le mode0, les zéros triviaux et l'archimédien sont traités par cette spécialisation, plutôt que perdus dans une erreur. Le noyau C^12 compact de ROLE1 isole exactement n+m=N aux entiers. Les deux contributions mixtes ont signe− et la double somme signe+. Ce sont des dérivations de la normalisation exposée par [Bombieri, sectionV,p.8](https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf) ; pas une formule explicite supposée nouvelle, ni une nouvelle définition de D_N.

L'audit a réparé le multiplicateur : (1−E²)^3 ne donne pas automatiquement(1+γ²)^3. Avec E=x∂x, (2−E)^6 a l'adjoint(2+ρ)^6 et |2+ρ|^6≥(1+γ²)^3 pour0≤Reρ≤1. L'opérateur double utilise6+6dérivées, compatibles avec C^12. Les facteurs2^r des transitions de largeur1/2 sont présents dans les majorants de χ_N. Les normes B_x,B_y,B_K sont construites par sommes rationnelles explicites ; elles ne sont pas des constantes libres ajustées au résultat.

Le compte N_+(t)≤tlogt, t≥10, est un relâchement inconditionnel du [Corollaire1 de Trudgian](https://arxiv.org/pdf/1208.5846). Compter les deux signes avec multiplicité, puis intégrer w(t)=(1+t²)^(-3) par Stieltjes, donne

    E_Z(T)=12T^(-5)(logT/5+1/25), T≥10,
    Zbar=20log10+E_Z(10),
    E_N(T)=(Bbar_x+Bbar_y+2Bbar_K Zbar)E_Z(T).

Le compte au bord se définit par limite à droite. La queue omise hors du carré spectral paie à la fois les deux axes et leur intersection ; remplacer le budget dépendant de Z_≤T par2Zbar E_Z est sûr et continu.

Diagnostic papier, sans calcul expérimental : à δ=1/4, le seul terme j=l=r=s=a=b=6 du majorant positif donne Bbar_K≥2^23N^13. Comme Zbar>20 et E_Z≥(12/25)T^(-5), l'expression de certificat vérifie

    E_N(T)≥(96/5)2^23N^13/T^5.

Pour N=10^8,T≤3·10^12, cette expression dépasse10^49. La tolérance1/100 demanderait déjà T>10^22 avec les normes proposées. C'est une borne inférieure sur la valeur du MAJORANT choisi, pas sur l'erreur réelle. Verdict NON_INFORMATIVE_BOUND ; aucune falsification de W2. Le calcul naïf exigerait toutes les boîtes de |Z_T| zéros et |Z_T|²intégrales doubles.

Un contrôle de mutation démontre le défaut de discrimination : sur une bande intérieure, A(K_N)≥(25/36)(3/4)^13δ(N−6)>1024. Une enveloppe10^49 ne pourrait distinguer l'omission de ce fond positif. Il faut une nouvelle norme, un traitement de l'oscillation ou une accélération prouvée avant un banc global utile.

## 3. Annexe Weil lissée, réellement distincte

Poser Y=√N=10000 et f_Y(x)=(x/Y)e^(−x/Y). Cette fonction appartient au domaineW complet : O(x) près de0 et décroissance exponentielle à∞. Sa transformée vaut Y^sΓ(s+1), et les modes0/1 sont1,Y. La proposition exacte de ROLE1 est

    H_Y=Σ(n≥2)Λ(n)[(n/Y)e^(−n/Y)+(1/(Yn²))e^(−1/(Yn))]
       =1+Y−ΣρY^ρΓ(ρ+1)−(log4π+γEuler)f_Y(1)
        −∫₁∞[f_Y(x)+f_Y(1/x)/x−2f_Y(1)/x]/(x−x^(-1))dx.

Au bordx=1, le quotient a limite f_Y(1)/2 ; il faut coder la valeur régulière et une enclosure près du bord, sans division d'un intervalle contenant0. Aucun mode de saut n'est effacé, f_Y étant lisse. Toutes les puissances premières sont présentes. La rotation gamma±π/4 fournit |Γ(β+1+iγ)|≤2e^(−π|γ|/4), β∈[0,1], sans RH. La série de zéros devient absolument convergente.

Avec a=π/4,T≥10, la queue auditée est

    E_H=4Y e^(−aT)[TlogT+(logT+1)/a+1/(a²T)].

L'intégration par parties de a∫_T∞ tlogt e^(−at)dt donne exactement cette enveloppe, après majoration1/t≤1/T. Les coupures X,Q,R≥2 de ROLE1 donnent

    E_primal≤e^(−X/Y)[(X+Y)logX+Y+2Y²/X],
    E_dual≤(logQ+1)/(YQ),
    E_arch≤(4/3)[e^(−R/Y)+1/(2YR²)+2/(YR)].

Le primal suppose la décroissance de sa fonction majorante au-delà deX, satisfaite pourX=10^6,Y=10^4 et à prouver comme garde. Le dual et l'archimédien ont leurs domaines explicites. T=100 et X=Q=R=10^6 semblent compatibles sur papier avec une erreur1/100 ; cette projection n'est pas une évaluation certifiée.

Ressources nécessaires : liste complète et multiplicité des zéros jusqu'à100, argument principal/Turing ou un compte équivalent certifié ; boîtes de Γ et Y^ρ ; intégrale archimédienne régularisée ; référence Λ neuve jusqu'à10^6 avec primalité/composité/powers certifiées ; arithmétique exp/log/π/γEuler. Au plus le compte conservateur100log100 borne le nombre de boîtes positives à couvrir. Les données actuellement lues ne constituent pas un jeu de boîtes prêt à l'emploi.

Contrôles réellement discriminants à cette tolérance : omission du modeY déplace de10000 et celle du mode0 de1. Omettre les puissances premières n'est pas anodin : le seul n=8192=2^13 a une contribution primale >1/10 par ln2>1/2 et e^(−8192/10000)>1/4. En revanche une petite contribution duale isolée peut rester sous1/100 ; il faut signaler cette limite de résolution, sans annoncer que toutes les mutations sont détectées.

## 4. Diffusion modulaire : normalisation, queues et alias

Le vrai réseau non primitif E_full=(1/2)Σ_(m,n)≠0 y^s/|mz+n|^(2s) converge absolument pourRes>1. Le mode m=0 donne ζ(2s)y^s. Pour m≠0, le recouvrement de multiplicité|m| annule le jacobien1/|m| ; les deux signes de m annulent le facteur1/2. Le mode constant est ζ(2s)y^s+A(s)ζ(2s−1)y^(1−s), A=√πΓ(s−1/2)/Γ(s). Diviser parζ(2s) normalise l'onde entrante, sans série1/ζ, inversion ou totient. La convention de réseau est celle de [Lagarias–Suzuki, équation(1)](https://arxiv.org/pdf/math/0412039). L'identification de cette solution à la vraie diffusion du domaine Friedrichs nécessite encore la résolvante et l'unicité ; elle ne devient pas un axiome.

Avec φ=Aζ(2s−1)/ζ(2s), L=−ζ'/ζ et ψ=Γ'/Γ, l'audit de la dérivée logarithmique confirme

    D(w)=1/2[ψ(w/2)−ψ((w+1)/2)−φ'/φ((w+1)/2)]
        =L(w)−L(w+1).

Les lignes Rew≥2 excluent les pôles gamma et les zérosζ ; la borne|ζ(w)−1|≤3/4 suffit ici. La série de L_K=L(w)−L(w+K) produit P_K(t)=ΣΛ(n)(1−n^(−K))e^(−nt), donc |F−P_K|≤C(K) pourK≥2, où C est la queue logarithmique entière fermée de ROLE2. L'identité reste auxiliaire à un estimateur favorable de D_N.

Pour Re t≥η,|Imt|≤π, Log principal, δ=π/2−arctan(π/η)>0. La relation gamma exacte, obtenue de [DLMF5.4.3](https://dlmf.nist.gov/5.4.E3) et de la récurrence, donne |Γ(2+iy)|≤6y²e^(−π|y|/2) pour|y|≥1. Employerδ=π/2 sur tout le contour serait incorrect. La queue intégrale et la vraie queue discrète E_J de ROLE2 ont les facteurs corrects, notamment j0=J+1 et h³.

La formule de Poisson-Mellin proposée utilise g(v)=e^(2v)P_K(te^v). Les signes de Fourier sont compatibles aprèsj↦−j. Toutes les dérivées de g doivent être Schwartz : à−∞, les majorants de dérivées de chaleur doivent compenser e^(2v) ; à+∞, e^(−ηe^v) domine. La seule décroissance de g ne suffit pas. Les alias l<0 et l>0 sont explicitement payés, avecηe^a≥4a,a=2π/h≥log2. Cette fermeture supprime un ε_quadrature libre, mais ne fournit pas les enclosures numériques de Γ,ψ,ζ et des quotients.

Au cercle complet M>N, l'alias est exactement Σ(k≥1)G_(N+kM)e^(−ηkM). La majoration G_l≤(l³−l)/6 donne l'enveloppe sur TOUS les coefficients supérieurs de ROLE2. Les alias négatifs sont exclus seulement parM>N ; une FFT ne serait pas automatiquement sans alias. Propager l'erreur de F impose

    e^(ηN)(2B_F ε_F+ε_F²)+A_circle+ε_outer_round,
    B_F=e^(−η)/(1−e^(−η))².

Pourη=8logN/N, l'amplification est exactementN^8=10^64 àN=10^8. Une erreurε_F=10^(-8) seule ne garantit donc pas une erreur10^(-8) sur G_N. Il faut construire ε_F≤τ/[4N^8B_F], puis payer séparément son carré, l'alias et l'arrondi.

Les paramètres globaux proposés K512,h1/128,J1280000000000,M100000001 représentent M(2J+1)évaluations de signal avant les rangsK. Aucun calcul de cette ampleur n'est autorisé ni annoncé praticable. L'annexe réelle t_ann=64logN/N,K64,h1/32,J4096 a8193nœuds et une référence exhaustiveΛ sur1..N, avec queue R_N fermée. Cette couche évite l'amplification du coefficient mais demande encore les fonctions complexes certifiées ; une référence normale de primalité ou puissance première doit être produite fraîchement, sans replay d'une banque de crible.

## 5. Puissances premières et référence indépendante

R_Λ(N) est une somme ordonnée. Poser Q(n)=Λ(n)−(logn)1_Prime(n). Le retrait propre est

    PP_N=Σ[n+m=N](Q(n)θ(m)+θ(n)Q(m)+Q(n)Q(m)).

Il correspond à l'union «n oum puissance première propre» : les couples power/power sont retirés une seule fois. Les deux premiers mixtes sont des classes disjointes ; soustraire deux sommesΛsuraxes puis ajouter leur intersection serait une autre écriture à vérifier, sans double retrait. Endpoints, p=q, Λ(1)=0, poidslogarithmiques et somme ordonnée restent visibles. La même référence peut vérifier R_Λ=R_θ+PP, mais ne prouve pas un estimateur D_N.

Une référence directe est autorisée : certification entière de primalité par divisibilité ou certificats déterministes, exacts powers p^k, composités avec diviseur et exhaustivité des indices avant filtres. Aucun ancien résultat ou producteur n'est un oracle. Les exp/log de poids demandent des enclosures séparées ; seule l'égalité des indices et classes est entière. Tous les coefficients l>N intervenant dans l'alias sont payés par l'enveloppe, sans copie d'une fenêtre ancienne.

## 6. Zéros, évaluateur autonome et interfaces de certificat

Chaque boîte de zéro doit porterβ_lo,β_hi,γ_lo,γ_hi rationnels, multiplicité, méthode d'isolation, preuves de non-annulation sur son bord, rang et hash de provenance. Il faut un compte GLOBAL égal à la somme des multiplicités, une séparation de la hauteurT des boîtes, les deux signes ou une conjugaison prouvée, et un traitement des bords. Une liste de décimales surβ=1/2 n'est pas un certificat de complétude. [Platt–Trudgian](https://arxiv.org/pdf/2004.09765) vérifient rigoureusement une hauteur très grande, mais expliquent qu'ils ont compté les zéros sans conserver leur isolation à haute précision ; ce résultat ne fournit pas par lui-même les boîtes nécessaires au noyau.

Le runtimePython connu a été inventorié en lecture seule : numpy2.3.5,pandas3.0.1,cffi2.1.1 sont présents ; aucun répertoire flint/arb/mpmath/sympy/gmpy/interval dans ce site-packages. Cela ne prétend pas inventorier toute la machine. Aucun import n'a testé une API. Une voie autonome demeure possible et doit être préparée avec ses preuves de restes :

* Exp/log/sin/cos/atan/π : séries à réduction d'argument rationnelle et restes géométriques ou alternés, enclosures extérieures ; aucun Decimal implicite supposé exact.
* Γ : intégrale Laplace en coordonnéev=logu, tronquée avec erreur près de0 et∞, puis quadrature par dérivées ou Taylor certifiés ; rotation pour les bornes ne vaut pas une évaluation sans erreur. Pourσ∈[1,2], queues≤ε^σ/σ et(R+1)e^(−R). Les argsψ requièrent leur série/reste séparés.
* ζ,ζ' : Euler–Maclaurin et Bernoulli rationnels avec reste intégral et sa dérivée ; voir les formes exactes dans [DLMF25.11](https://dlmf.nist.gov/25.11). Ne pas tronquer un développement asymptotique sans norme du reste. Un majorant coefficientiel explicite des Bernoulli périodiques peut éviter une constante libre.
* Complétude àT100 : compter le vent de g(s)=(s−1)ζ(s) sur un rectangle incluant la bande, avec g(1)=1, boîtes de contour excluant0 et variations certifiées. g évite le pôle1 ; les zéros triviaux hors rectangle restent exclus par domaine. Des signes de la fonction complète sur la droite peuvent isoler des zéros, mais seuls le compte et l'égalité des multiplicités donnent la complétude sans RH supposée.

Une première source Γ/ζ n'est pas READY tant que ses dérivées, contours, queues, branches et quotient non nul ne sont pas fermés. Les annexesH_Y/HEAT ne sont pas abandonnées ; leur préparation suit le premier banc sans refaire une vieille expérience.

L'interfaceLean doit définir les vrais objets et les gardes, puis prouver : primitive et FTC, finite_sum/endpoints/isométrie, domination/Tonelli/p-série, enclosures sqrt/outward ; formuleWeil complète et compte des vrais zéros ; normes construites et queue ; Laplacienne fermée, Friedrichs, Eisenstein non primitif, résolvante et unicité ; Mellin et Poisson sous vraies hypothèses ; erreurs de quotient/extraction/alias ; retraitPP et raccord au bilan. La lecture ciblée du cache a trouvé des déclarationsζ, Mellin et inversion, sans formuleWeil/compteglobal identifié dans les répertoires cherchés. Ce n'est pas une preuve d'absence globale. Rien n'a été élaboré ou compilé.

Les voies Fredholm/Birman–Krein restent OPEN : espace, domaine, paire d'opérateurs et différence de résolvantes doivent être construits ; classe de trace ou renormalisation HS avec contre-termes explicites, norme de queue finie construite, contour et extraction sont nécessaires. La surface modulaire a un continuum ; le canal scalaireφ n'est pas la trace de sa chaleur entière. Les contributions discrète/continue, identité, elliptique et parabolique apparaissent séparément dans [Booker–Platt, formule de trace](https://arxiv.org/pdf/1710.00603). Aucun déterminant n'est défini pour recopier la réponse, et aucune positivité/RH/Hilbert–Pólya n'est supposée.

## 7. Un seul banc auxiliaire préparé et règles de verdict

Les sources du premier banc sont `role6/interval22.py`, `epstein_bank22.py`, `epstein_contract22.json`, `epstein_paper22.md`, `run_epstein_once22.py`. Tous les24cas sont fixés avant filtre :18originaux y1/2,1,2 avecm±1,±2,±7,Q4096 et all-shifts+endpoints ;6échelle y10000,Q2^20 avec endpoints seulement. Les formes et gardes ont été vérifiées sur papier parROLE2 et relues parROLE3. La précision96bits, tolérance1/100000 et cap de queue1/1000000 sont antérieurs à toute exécution. La compression n'est pas comptée comme une exhaustivité d'évaluations individuelles.

Les enclosures de la valeur de gauche et de la cible doivent être suffisamment étroites ET compatibles. Un chevauchement trop large est UNRESOLVED_NON_INFORMATIVE ; il n'est jamais FALSE. Une disjonction originale serait NUMERIC_COUNTEREXAMPLE_AUX avec les gardes et la provenance complètes, à diagnostiquer. Les mutantsq>1 doivent être disjoints ; q=1 reste dans le catalogue avec mutation non applicable. Un futur PASS se nommera uniquement EPSTEIN_UNFOLDING_AUX_PASS. Aucun certificat de coefficientN, de chaleur, deWeil, compilation ou gainD_N ne sera crédité par cette annexe.

Avant toute invocation : gelSHA sources/contrat/inputs/runtime, FULL review root, sélection propre et porte distincte `round22_epstein_authorization.json`. Le lanceur crée atomiquement l'unique réservation après gate, capture les bytes PREEXEC, consigne START réel/commande/log/exit/reçu et vérifie POSTEXEC les bindings. Il n'y a ni deuxième préflight, ni capture après exécution appeléePREEXEC. Toute mutation retire le crédit. La préparation ne crée ni répertoireactual, ni résultatPASS, ni log simulé.

Ce précontrat ne clôt pas le livrable global. Le coefficientN, une information quantitative favorable sur la corrélation, le retraitPP complet et son raccord aux charges de D_N restent ouverts. La cible D_N≤N/(256logNloglogN) n'est ni prouvée ni testée par le sous-banc préparé.
