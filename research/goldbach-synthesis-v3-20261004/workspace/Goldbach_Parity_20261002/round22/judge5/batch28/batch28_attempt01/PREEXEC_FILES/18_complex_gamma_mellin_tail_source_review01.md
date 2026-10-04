# Revue indépendante SOURCE — queues Mellin de Gamma22

ROLE5, revue SOURCE/PAPER uniquement. Verdict : chaîne mathématique cohérente et aucune incompatibilité précise d'API identifiée dans les signatures lues. Le module n'a pas été élaboré ou compilé par cette revue ; aucun PASS n'est attribué. Baseline officielle observée par ROOT27 :85 modules/1434 déclarations auxiliaires. Aucun lot28, PREP, candidat importé, calcul numérique, test de tactique ou ancien rejeu créé ici.

Paquet auteur figé dans `D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_tail_source01`. Source complète lue sans troncature FULL57724b ; contrat, catalogue, lectures et handoff complets FULLd79077. Contrôle physique167c46 :19/19 bindings inchangés, tous octets SHA vérifiés ; ceci n'est ni une lecture FULL des11 fichiers cache ni une fermeture exhaustive d'imports.

| Objet | SHA256 |
|---|---|
| ComplexGammaMellinTail22.lean |7dcce5beacdadc61dd067f9a6e176d70d5ff3c44cb6720b6f1d650068b67dcd5|
| source_contract22.md |35c816f307b724beb597c77115157a1503daaed80bba596e9d5682699a8cdca8|
| source_catalog22.json |2292627179524c8743c52a6295dc8e5361e64999af5e0b90f0a72375b90d3fe5|
| source_read_receipts22.json |1586831e195de9100fd7a33bb76054eedab077bd233f835a04365120f431db13|
| source_handoff22.json |b80e83e1029995309836b313b5897a54ec5c27c07cb6e2a48371705c4cf41587|

La lecture manuelle confirme22 déclarations et22 impressions qualifiées exactes :4 définitions (`signedGammaTail`, `complexGammaTail`, `complexGammaTailRadius`, `complexGammaTruncated`) et18 théorèmes. Les seuls imports sont Local22, `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals` et `Mathlib.MeasureTheory.Integral.SetIntegral`. Aucun `sorry`, `admit`, axiome ajouté, `unsafe` ou `native_decide` n'est introduit. Les dépendances d'axiomes effectivement utilisées par ces22 déclarations devront être constatées par une future compilation ; les prints SOURCE ne suffisent pas à ce constat.

## Objets, deux signes et constante

Le noyau est le véritable `Complex.Gamma(2+it) * w^(-(2+it))`, avec cpow principal. Local26 sourcee54cac5b2ab3996eb7bb86165448e0eff4c837b2fbda0af923e454962e526e08, olean364ac79a2fb46546da4ffdb94993479ce90bbb861c5c5cd27e253cbc5f1968b5, fournit déjà la domination sur toute la droite réelle :

`||K(w,t)|| ≤ C(w) exp(-δ(w)|t|)`, où `η=(π/2+|Arg(w)|)/2`, `δ=η−|Arg(w)|=(π/2−|Arg(w)|)/2>0` et `C=||w||^(-2)/cos(η)^2>0` pour `Re(w)>0`.

Le nouveau module reconstruit l'intégrabilité sur `(H,+∞)` depuis le vrai Laplace réel à tauxδ, puis la mesurabilité par continuité de chaque intégrand signé. Il n'offre pas `Integrable` ou le majorant final en hypothèse. Pour `H≥0`, les points du domaine ont `t>0` et les deux signes vérifient `|±t|=t`. L'intégrale réelle `∫_(H,∞) exp(-δt) dt=exp(-δH)/δ` est obtenue par changement d'échelle positif ; cette évaluation auxiliaire accepte H réel quelconque.

Chacune des deux normes d'intégrales signées est donc bornée par `C exp(-δH)/δ`. La norme de leur somme est majorée par la somme des normes, puis multipliée par la norme réelle positive de `1/(2π)`. Le rayon final `R(w,H)=C exp(-δH)/(πδ)` a exactement ce facteur1/π ; aucune annulation favorable des deux signes n'est supposée. Il s'agit d'une majoration de norme d'une erreur analytique, pas d'une nouvelle positivité arithmétique.

## Identité de troncature et domaines

La négation préserve le volume de Lebesgue. L'API `integral_comp_neg_Ioi` produit d'abord `Iic(-H)` ; l'égalité `integral_Iic_eq_integral_Iio` retire le point de mesure nulle. La queue négative vaut ainsi l'intégrale sur `(-∞,-H)`, et non un objet abstrait offert. Le complément de `[-H,H]` est l'union de cette demi-droite et de `(H,+∞)`. Elles sont disjointes pour H≥0, y compris H=0. L1 de Local26 et les ensembles mesurables justifient `setIntegral_union` et `integral_add_compl` sur volume réel. La conclusion exacte SOURCE est

`complexGammaInverse(w) − complexGammaTruncated(w,H) = complexGammaTail(w,H)`,

puis sa norme≤R, avec seulement `Re(w)>0` et `H≥0`. H négatif n'est pas couvert par cette identité de queues disjointes. La source ne remplace pas `complexGammaInverse` par `exp(-w)` et n'importe pas Holomorphy27. Ce raccord aval est désormais disponible comme vrai théorème indépendant27 ; il demeure absent de ce module, sans identité finale supposée en prémisse.

## Continuité et uniformité : portée exacte

La source construit la continuité deη,δ,C depuis Arg continu sur le demi-plan droit/slitPlane, la norme non nulle et cosη>0. Elle obtient la continuité **jointe du rayon fermé R**, pour `Re(w)>0` et tout H réel, ainsi que sa positivité et sa monotonie décroissante en H. Les divisions par cosη et πδ sont justifiées ; aucune uniformité jusqu'au bord `Re(w)=0` n'est annoncée.

`exists_local_uniform_Gamma_tail` construit une vraie boule autour de w, depuis les voisinages `Re(z)>0` et `R(z,H)<2R(w,H)`. Pour ce H≥0 fixé et tout T≥H, la norme de la queue est≤`2R(w,H)`. ε dépend du centre et de H ; l'énoncé n'offre pas une seule boule indépendante de H à l'infini.

La continuité jointe de l'intégrale complexe à seuil mobile n'est pas démontrée, et une inégalité par un rayon continu ne l'implique pas seule. Le théorème Lean de limiteR→0 ou de convergence localement uniforme H→∞ n'est pas présent non plus. Ces absences sont déclarées explicitement dans le contrat et ne constituent pas un déficit de ses22 énoncés. Sur papier, la limite ponctuelle du rayon découle deδ>0 ; aucun crédit formel de ce prolongement n'est donné ici.

## API et provenance contrôlées

Sources primaires du cache4.15/mathlib9837ca9d, lectures **TARGETED** seulement :0d6d27 vérifie ImproperIntegrals1–68, IntegralEqImproper1081–1108, Lebesgue/Integral75–120, SetIntegral97–181/719–747 ;1a04fa vérifie Bochner817–828/1328–1339, Pow/Continuity263–274, Topology/Constructions581–583, MetricSpace/Pseudo/Defs698–713, Interval/Set/Basic381–386, Field/Basic169–176, Trigonometric/Basic436–442. Les SHA correspondants concordent tous aux19 bindings du handoff. Ce sont les signatures exactes des évaluations, changements de variable, découpages, continuités et voisinages employés.

Contrôles supplémentaires ciblés :325257 donne la signature Bochner1360–1365 de `norm_integral_le_integral_norm`; cfd2f0 et6b8846 donnent L1Space432–438, `Integrable.mono'`, fichierSHA7d041392ff5a34fb256b5ce97cc04b8c681919350c849647d4309bdc29af4a2a. Le chemin initial supposé `MeasureTheory/Function/L1Space/Integrable.lean` était absent ; cette recherche est exclue de toute prétention de lecture. Le fichier réel est `MeasureTheory/Function/L1Space.lean`.

Local26 definitions/domaines/rotation1–87 et GammaPrerequisites02 Laplace38–63 ont été relus TARGETEDa0cbd1, puis les signatures de domination/continuité/L1 Local26 TARGETED6b8846. Les preuves intégrales du nouveau module ont les charges mesurabilité/domination/domaine adaptées aux API lues. Cette vérification statique ne prédit pas un exit0 et n'exerce ni résolution d'imports, ni élaborateur, ni tactique.

Local26 reste le seul import local direct ; ses dépendances transitives readonly sont ThermalGammaMellinInverse20 et GammaPrerequisites02. Le reçu26 globalFAILED53201e46ee6a6418915358d37a61655a286bd2d814930d0fe68520fec4c92cdb reste intact : le module Local seul a réellement PASS22, conservé et crédité par ROOTpartial9b7697d2d35d12903e436403e77fb44e8ea76c6f586940e28d168ab851340e9b. Aucun crédit de l'ancien Holomorphy02 échoué n'est utilisé. Tous les19 bindings courants sont conservés ; aucun ancien fichier modifié.

Aucune queue deζ/ζ′, échangeΛ, compte de zéros, trace Weil globale, signe angulaire canonique, correction PP, coefficientN=10^8, D_N ou WIN n'est acquitté. Avant un éventuel lot distinct, sa sélection ROOT puis fermeture d'imports/cache et gate de compilation restent nécessaires. La revue ne crée aucun lot ou manifeste de préparation.
