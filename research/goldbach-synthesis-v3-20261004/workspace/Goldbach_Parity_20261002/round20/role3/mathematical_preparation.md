# ROLE3 — revue indépendante et plan de formalisation 20 / 13.12

Statut : préparation papier et sourcewriting sélectionnés ; aucune compilation Lean, aucun producteur numérique, aucun ancien PASS réexécuté. Ceci n'est ni FINAL3 ni une victoire. Le seuil source reste u=log N >=10^24. Les acquis et les1808 archives restent immuables.

Lectures intégrales : skills executor/merge-eval (65da8a), PROBE20 (2f9ea5), FINAL1_20 en deux portions a89e5a/75411a ; SHA FINAL1 actuel1c52ccfe6aaf393fe02b606ecbaeb56ae62810f0b93d6db604672ba560a241d9. Contraintes fraîches FULL a45a0c :35 findings,5 pruned,maxdepth2. La sélection13.12 réelle a été reçue puis lue FULL506a0d, et le prompt FULL1d6533. L'ancien eval_cmd19 inclus dans le prompt est un historique ; il ne sera pas exécuté. Le contexte explicite20 impose un nouveau banc, une gate numérique puis une gate compile.

## Résultat de la revue mathématique

Les identités B1–B5 et l'inégalité pointwise B2 sont cohérentes avec le vrai support, sous les gardes indiquées ci-dessous. Je n'ai trouvé aucun contre-exemple mathématique à ces identités pendant cette revue papier. Cela n'est pas une validation numérique. SD reste entièrement non prouvé, et la comparaison favorable du principal total à M0 reste ouverte. Les gardes ci-dessous doivent être construites ou apparaître comme prémisses arithmétiques explicites, jamais comme une prémisse de petite Gamma.

### B1 : vrai poids et masque premier

Pour un candidat j>z>=1, le support Selberg doit être descendant pour divisibilité, contenir1 et exclure0. La définition explicite de la section10 est correcte : en inversant y_m=mu(m)/(r(m)G), on obtient mu(m/k)*mu(m)=mu(k), car m est carré-libre et k|m. Ainsi le facteur mu(m/k) n'est pas oublié ; il est absorbé dans mu(k). La division par G n'est justifiée qu'après G>0. N pair exclut le premier2 du support unitaire, donc chaque facteur réel p-2 de r(m) est strictement positif. z>=1 assure le terme m=1 de G égal1. Ces deux gardes sont essentielles pour le modèle réel, même si Lean permet une division par zéro comme opération totale.

Sur un j premier>z, seul k=1 divisej dans le support, et lambda1=1 doit être dérivée de la définition, non fournie par une hypothèse. Sur un composite j>=2, logj fois le carré est positif et entièrement soustrait. L'identité B1 utilise theta, donc une puissance propre p^e est bien dans la masse composite. Le raccord raw conserve ensuite le vrai vonMangoldt, sans mu(j)^2 sur cette mesure.

### B2–B3 : vrai ensemble premier, minFac et cellules non minimales

La primoriale effective est le produit du Finset des premiers ell<p avec ell ne divisant pas t*N. Il est carré-libre et non nul. Pour v unitaire à t*N, l'ensemble effectivement rencontré est sa rencontre avec les vrais primeFactors de v, ou équivalemment le filtre ell|v. Son cardinal r n'est pas un paramètre libre.

Les diviseurs h de la primoriale correspondent bijectivement aux sous-ensembles de ces premiers distincts. Leur mu(h) vaut(-1)^card. Grouper les sous-ensembles de cardinal i donne la somme de binom(r,i), avec la convention choose=0 hors du cardinal. La somme jusqu'à2K+1 vaut1 si r=0 et -choose(r-1,2K+1) sinon. Le signe négatif est indispensable. Aucune hypothèse L>=0 n'est vraie en général.

Pour j>=2 composite, p=minFacj est premier, p|j, p²<=j, et v=j/p>=p. Aucun premier ell<p ne divisev. Réciproquement, p premier, p|j, p²<=j et roughness(v) impliquent p=minFacj, quand tous les facteurs de j sont unitaires à t*N. Il n'est pas demandé (p,v)=1 : j=p² est couvert. Si une cellule développée utilise un p non minimal, le vrai plus petit facteur ell<p de j ne peut pas être p et divise donc v ; la cellule roughness est nulle et L<=0. Supprimer cette cellule signée modifierait C_minus et le slack.

La différence C_true_low-C_minus est exactement la somme pondérée des roughIndicator(v)-L(v), sur toutes les cellules développées p|j,p²<=j,p<=P*. Elle est >=0 par le vrai poids logj*(sum lambda)^2. La queue de minFac>P* reste une somme physique positive séparée. Une identité finie peut conserver une queue grande ou vide ; aucune petitesse n'en résulte.

### B4 : portée de la borne grossière

La preuve annoncée utilise kappa_c<=2u, logj<=u et sum|lambda|<=B_lambda. La borne sur kappa nécessite l'acquis source S(N)<3logu et le comparatif élémentaire3logu<=u au seuil1e24. Les vrais t sont distincts par factorisation canonique et t<N/a ; la somme harmonique N sum1/t plus le nombre de t paie les +1. La majoration B4 est cohérente, mais trop grande pour le budget terminal. Elle n'est pas sélectionnée comme crédit analytique nouveau.

### B5 : quotient par gcd puis lcm, sans coprimalité fictive

K0=lcm(k,l) est carré-libre quand k et l le sont. Le lemme acquis19 `remaining_face_modulus_iff` donne directement K0|(p*v) iff K0/gcd(K0,p)|v sous p!=0. La preuve de quotient n'est donc pas à réinventer. `Nat.lcm_dvd_iff` rassemble h|v et Kp|v en H|v. Comme j=p*v, H|v iff p*H|j par cancellation positive. Cela conserve p|v et toutes les répétitions du candidat.

La congruence doit être transportée avec j=N-t*q et t*q<=N explicitement ; une soustraction naturelle tronquée ne remplace pas une égalité dans Z. La garde du front original fournit t*q<N sur les vrais axes. Pour une cellule physique, coprime(j,t*N)=1 est dérivée de coprime(t*q,N)=1 et j=N-t*q, avec coprime(t,N)=1 extrait de l'unité du produit physique. Si nu partage t, le facteur commun ne divise pas N et la congruence est impossible. Si nu partage N mais pas t, un q admissible devrait partager N, ce que le domaine physique interdit. Ainsi les modules incompatibles sont réellement nuls, pas des AP aux coefficients simplement oubliés.

Nu=p*lcm(h,Kp) ; un produit p*h*k*l est faux en cas de recouvrement. La fenêtre des composites est la vraie J_t intersectée avec p²<=N-tq, donc q<=floor((N-p²)/t). Les cas v=p et p²=j restent inclus. La branche vide garde son principal conventionnel0 et son reste0. Aucun plafond de multiplicité19 n'est transféré.

### B6–B9 : variation cohérente, portée analytique distincte

B6 est cohérent sur papier : q0>a>1 et q0-1>=a, N-ty>0 sur l'intervalle d'intégration, f(y)=log(N-ty)/logy est positif décroissant et <=16/7<3. La sommation partielle avec erreur cumulative E(y) donne une borne2 supf * E<=6E. Retirer les premiers q|N coûte au plus supf*sum_{q|N}logq<=3u, donc6(E+u) convient. La constante u ne constitue pas une erreur Möbius. Cette dérivation doit être formalisée en analyse réelle avant de revendiquer B6 comme théorème Lean.

Pour la première formalisation, l'AP réel sera défini comme une somme finie de log(N-tq), son principal par l'intégrale réelle et sa phi réelle, puis son reste exactement comme leur différence. Les identités principale+reste et la majoration par la somme des valeurs absolues de ces vrais restes ne nécessitent aucune prémisse B6/SD. Elles ne paient pas le reste. L'erreur intégrale/endpoints0 éventuelle doit rester visible.

Le coût Bonferroni est nu<=p^(2K+2)*z², puisque h utilise au plus2K+1 premiers< p. Avec K=1, c'est p^4 z² ; le diagnostic p³ appartient à un autre crible inférieur. B9 est une garde suffisante de niveau, pas un théorème BV ni une estimation signée. Les grands modules et les grands p restent dans le complément. Le budget conditionnel deSD n'est pas une preuve deSD ; aucune déclaration Lean ne recevra SD comme axiome ou comme hypothèse de victoire.

### Section10 : p0 réel, principal positif et compensation

Le symbole cache est `GoldbachRound16.Anchor.leastMissingOddPrime` (namespace confirmé452a58), avec `leastMissingOddPrime_spec` sous N!=0 et EvenN. Son spec dit que tous les premiers ell<p0 divisent N, incluant2 via EvenN. La primoriale effective pour p0 est donc vide. Sur les candidats unitaires, L(v)=1. Si p0|t, j est unitaire à t et la branche p0|j est impossible. Si p0 ne divise pas t, p0 ne divise pas N et les lambda de section10 excluentp0 ; K0 est premier à p0.

La garde p0²<x/2 doit être raccordée à A7, S(N)<3logu et u>=1e24, ou gardée comme garde arithmétique locale indépendante. Elle n'est pas certifiée auN fini par un testsource. Quand cette garde est vraie, l'intersection p0²<=j ne rétrécit aucune fenêtre de la tranche. `Nat.totient_mul` et `Nat.totient_prime` donnent phi(p0*K0)=(p0-1)phi(K0), d'où le principal I_t*Q_t(lambda)/(p0-1). Le facteur kappa_c est ajouté dans la somme physique globale, et n'est pas omis par une normalisation silencieuse.

Le coût d'exclurep0 dans le coefficient Euler est compensé par le retrait1-1/(p0-1). Ce diagnostic concerne un coefficient logarithmique idéal ; il n'est ni une asymptotique uniforme en tN, ni une borne finie. Une formalisation du facteur exact de phi et de la masse p0 ne prouve pas le signe favorable du principal total.

## APIs cache lus, et limites de preuve

Le type physique réel s'appelle `GoldbachRound18.SeparatedTypeII.PhysicalWitness`, sans suffixe18. Il contient c/r/s/q premiers, leur ordre, cs<=a<rs<q, crs>a, unité du produit, bulk et original_front. `theta` et `rawLambda` sont les définitions acquises de ce namespace. Le terme «PhysicalWitness18» dans la note est un label humain, pas une API.

APIs source vérifiés en lecture seule : `Nat.minFac_prime`, `Nat.minFac_dvd`, `Nat.minFac_le_of_dvd`, `Nat.minFac_le_div`, `Nat.minFac_sq_le_self`, `Nat.le_minFac`; `Nat.lcm_dvd_iff`, `Nat.coprime_div_gcd_of_squarefree`; `Nat.primeFactors_prod`, `Nat.prod_primeFactors_of_squarefree`, `Nat.primeFactors_div_gcd`; `ArithmeticFunction.moebius_apply_of_squarefree`, `moebius_eq_zero_of_not_squarefree`; `Finset.card_powersetCard`, `sum_powerset_apply_card`, `Int.alternating_sum_range_choose` ; `Nat.totient_mul`, `Nat.totient_prime`.

Le cache dispose déjà du Selberg fini17, notamment `principal_optimum`, `weight_empty`, `canonical_weight_formula`, `canonical_moebius_weight`, `weight_zero_outside`, support descendant. Cette preuve ne doit pas être réexécutée ou recomptée. Une spécialisation au vrai support t*N*p0 et g(p)=1/(p-1), avec raccord réel phi/product de primeFactors, est un usage d'acquis. Si un nouvel import Judge17 s'avère nécessaire, il sera annoncé et lié explicitement avant la compilation ; ne pas substituer un olean auteur20.

Les recherches rg qui ont touché des chemins cache inexistants (ArithmeticFunction était un fichier, pas un répertoire ; GCD/Lemmas absent) sont des erreurs de lecture résolues par rg --files. Ce ne sont pas des échecs Lean ou numériques. Aucun Lean a été lancé pendant cette revue.

## Plan de nouveaux modules, sans exécution autorisée

1. `OddBonferroniArithmetic` : vrais primeFactors/primoriale/diviseurs et cardinal rencontré ; somme tronquée, identité binomiale impaire, minorant roughness et slack non négatif. Un lemme combinatoire abstrait peut servir d'étape interne, mais la sortie doit connecter le poids aux objets arithmétiques réels.
2. `LeastFactorComposite` : vrai minFac, quotient>=p, carré<=j, roughness exacte/converse ; cellules non minimales négatives et p²/repeated primes conservés.
3. `SwitchedSelbergWeight` : coefficients construits sur le support unitaire t*N*p0 ; lambda1, poids nul horssupport, facteur phi/lcm et Q=1/G par spécialisation d'acquis. Pas de G petit/grand libre.
4. `PhysicalCompositeSubtraction` : domaine q premier obtenu des gardes physiques réelles ; B1 et B3 avec slack et queue définis, theta/raw explicites et front+1 exact. L'extraction des fenêtres et triples ne sera pas postulée par un ensemble libre à bonne incidence.
5. `CompositeAPConductor` : développement p/lcm/gcd et équivalence AP depuis le candidat, incompatibilité, bornes entières et branche p0/phi réelle. Coefficients signés conservés.
6. `SwitchedIncidenceEstimator` : vrai principal/restes AP et identité exacte, puis inégalité avec restes absolus et queue. B6 analytique et SD restent ouverts si non formalisés ; aucun transfert uniforme/budget au ledger n'est présumé.

Ces modules peuvent être réorganisés avant leur premier essai pour garder les dépendances propres. Chaque compilation nouvelle attend le PASS canonique neuf13.12 lu par root et sa gate concrète. Chaque vraie FAIL conservera sourcePREEXEC, commande, stdout/stderr/log et exit ; aucun PASS inchangé n'est rejoué. Le Juge compilera ensuite ses propres copies neuves avec les imports acquis immuables. Tous ces ingrédients restent auxiliaires tant que l'incidence et le ledger complet ne sont pas payés.

Mise à jour metadata avant sourcewriting : prompt13.12 corrigé vers le Judge20 planifié, SHA2e1aa422888fd4986e062edf8b8b9535179d48f7eec929cc1d2d1baf94e5d6af, relu FULL9da4cf. Le Judge20 n'est pas créé/autorisé. Aucun eval_cmd19 ou20 n'a été exécuté par ROLE3.
