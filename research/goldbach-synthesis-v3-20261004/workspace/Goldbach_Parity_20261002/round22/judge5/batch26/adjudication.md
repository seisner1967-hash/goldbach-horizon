# Adjudication indépendante — lot26

Statut réel INDEPENDENT_BATCH26_FAILED : un module PASS entier, ComplexGammaMellinLocal22, 22 déclarations auxiliaires (16 théorèmes, 6 définitions). ComplexGammaMellinHolomorphy22 échoue, zéro crédit sur ses 15 déclarations. Deux enfants réels, arrêt après cet échec, aucune reprise.

START global 2026-10-03T22:44:35.104994+00:00, FIN global 2026-10-03T22:45:51.497018+00:00 ; parent23b2e1/session53965→0bc7a2 exit1. Local START 2026-10-03T22:44:35.108996+00:00, FIN 2026-10-03T22:45:06.480563+00:00 exit0 ; Holomorphy START 2026-10-03T22:45:06.480563+00:00, FIN 2026-10-03T22:45:40.915145+00:00 exit1. Aucun timeout ni erreur de lancement.

Le vrai PASS Local construit Gamma(2+it) et la puissance complexe principale pour Re(w)>0. Rotation réelle ±η, η=(π/2+|Arg(w)|)/2, décroissance δ=(π/2−|Arg(w)|)/2>0 et coefficient ‖w‖⁻² sec²η ; continuité, intégrabilités sur les deux demi-droites puis volume réel, dérivée ponctuelle en w, accord avec le Mellin réel PASS20. Aucune intégrabilité ou conclusion finale supposée. Les deux dépendances readonly sont exclusivement GammaPrerequisites22 PASS02 et ThermalGammaMellinInverse22 PASS20, jamais recompilées.

Sept diagnostics techniques dans Holomorphy :142:4 exp(-(d*t)) face à exp(t*(-d)), normalisation arithmétique manquante ;145:68 addition de fonctions non réduite avant ring ;157:6 composition par la négation non réduite avant simplification ;224:16 et227:18 Tendsto inconnu ;232:10 Eventually.of_forall inconnu (namespace Filter absent) ;233:4 introN en aval des types récupérés. Ces diagnostics ne réfutent ni domination intégrable, ni holomorphie, ni identité analytique sur papier, et n'établissent aucune obstruction de parité. La réparation éventuelle doit être une nouvelle SOURCE sous sélection ROOT.

Couverture exacte :22/22 impressions Local, toutes [propext, Classical.choice, Quot.sound], aucune liste vide, récupération ou axiome personnalisé. Holomorphy :15/15 impressions, neuf standards et six sorryAx de récupération, toutes exclues du crédit de module. Ces six sont weightedExponential_integrable, localDerivativeEnvelope_integrable, complexGammaInverse_hasDerivAt, complexGammaInverse_analytic, complexGammaInverse_eq_exp, complex_exp_eq_Gamma_integral. Aucun native_decide/ofReduceBool ni avertissement ;37 noms exacts,31 standards au total ne valent que le crédit entier Local22.

Conservation physique après FIN :9020 inputs,1770 anciens Juge (dont lot21 ROLE4 clos),3089 archives,91 captures original/copie et deux dépendances readonly rehashés intacts. Gate/PRE/POST concordent ; Lean4.15/mathlib9837ca9d existants. Aucun olean auteur, ancien compile, numérique ou exécutable natif invoqué.

Baseline83 modules/1397 déclarations avant observation ROOT ; seul ajout possible1/22, soit84/1419 après cette observation. Pas de pleine inversion complexe compilée, H1/Weil/traceζΛ, uniformité en phase, correction PP, coefficientN=10^8, D_N ou WIN. Aucun lot27 préparé ici.

Reçu réel D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\judge5\batch26\batch26_attempt01\receipt.json SHA 53201e46ee6a6418915358d37a61655a286bd2d814930d0fe68520fec4c92cdb.
PRE ed18197b3a2dd96417630f08671f957f33491cdb492fcf6394556b8ee44ae482 ; POST 78a0ea4ba626eaf07ae1fb3159ca2d8aa9fc6a2a8935e7cc3accf55e1843568b.
Local source e54cac5b2ab3996eb7bb86165448e0eff4c837b2fbda0af923e454962e526e08 ; log de64611ca93c9f58c160f4f808a62328917df4b2b569ea3109f9d07fe64fd260 ; olean 364ac79a2fb46546da4ffdb94993479ce90bbb861c5c5cd27e253cbc5f1968b5.
Holomorphy source 9d3d050fab541086f1bf9932aa51d240dd3a72fcb194412f38e997ebeedd9d4a ; log edb1dec599f5671b8acd6517efd2551a23aba33717d6b69f3924adadd3928cfb ; aucune olean.

