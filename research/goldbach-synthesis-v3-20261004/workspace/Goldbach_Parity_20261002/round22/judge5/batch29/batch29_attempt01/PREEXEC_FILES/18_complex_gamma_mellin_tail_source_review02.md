# Revue indépendante SOURCE — Tail02

ROLE5. Verdict : aucune objection mathématique ou incompatibilité précise d'API identifiée dans cette révision. Il s'agit d'une revue statique, sans élaboration, compilation, import candidat, probe ou calcul numérique. Aucun PASS Tail n'est attribué. Baseline officielle :85 modules/1434 déclarations ; FAIL28 conservé, zéro crédit.

Paquet figé : `D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_tail_source02`. Source entière lue FULL09b792 ; contrat, catalogue, lectures et handoff entiers FULL3a22d3. L'appel agrégé initial tronqué est exclu de ces lectures FULL. Contrôle1e7462 : les29 bindings du handoff ont leurs octets et SHA actuels conformes ; cela ne prétend pas lire les fichiers cache entiers ou fermer leurs imports.

| Objet | SHA256 |
|---|---|
| ComplexGammaMellinTail22.lean |3002a4d39dfd6bd072f1a8f778de3752cf91bf60f831dd3345f5dd9631723852|
| source_contract22.md |bada33d12c4321a041cfe6fa2dd9c3bcf3cc53047676be519a85ba7b7e5713c3|
| source_catalog22.json |0e259314344d92066fd25f4ada0737fa8cb184d0af844ee764e3c7e16fa986da|
| source_read_receipts22.json |1010d969ddbd0b1d94443eaccb9231969f7e9421972860f65df508d26817acd4|
| source_handoff22.json |c929f867a5de2441ffaa0fdbcf138d1d89adc8b659ed3e87973fefdc10ba3b50|

La comparaison lexicale ligne à ligne1e7462 avec la copie indépendante28 confirme exactement trois sites de preuve modifiés. Les définitions, imports,22 énoncés et22 impressions qualifiées restent inchangés :18 théorèmes,4 définitions. Lecture manuelle des22 déclarations complète ; aucun sorry, admit, axiome personnalisé, unsafe ou native_decide ajouté. Les axiomes réellement employés devront être constatés par le futur Lean ; les prints écrits ne constituent pas une validation.

1. La variable `hmul : IntegrableOn ... (Ioi 0)` fixe la restriction, puis l'appel qualifié `IntegrableOn.mono_set` évite la recherche du champ sur `Integrable`. La signature réelle accepte précisément une preuve d'intégrabilité sur t et s⊆t. Avec H≥0, `Ioi H ⊆ Ioi 0`. Le majorant n'est pas une prémisse gratuite : il provient du Laplace réel indépendant à tauxδ.
2. `integral_add_compl` reçoit maintenant `(s := Icc (-H) H)`. Ses autres arguments fixent le vrai noyau et volume réel ; la mesurabilité et L1 sont déjà disponibles. Cela résout les implicites s/a/b observés dans le vrai log28, sans changer la décomposition intégrale.
3. La section `hp : ContinuousAt (fun z : ℂ => (z,H)) w` est explicitement typée. Le produit de l'identité et de la constante H, suivi de la continuité jointe au point(w,H), donne la section fixeH après `Function.comp_apply`. L'ancien choix erroné `Prod.mk w` au pointH est écarté statiquement.

Ces trois signatures primaires sont relues TARGETED7ba1dd : `IntegrableOn.lean:99–111`, SHA377d50adedf2a1705a1e4acc6126076e7b40c8213f0600fec8898f7a019e7492 ; `SetIntegral.lean:171–182`, SHA2fc90a7ecb3b4d9e47299a2b3b8eebf97a4e2a177d28daf3c48a4c0e059c4c86 ; `Topology/Constructions.lean:577–586`, SHAa2761653618b7e79b33969e83107d346e377233fd92a06601e315aa460cb1d1b. Les lectures et conclusions mathématiques inchangées de la revue01 SHA024dd84e4ed371175b90eef1bf4ef747b9050817e4675492bb7ac1e59745454d restent valides au niveau SOURCE ; son avis n'avait pas prédit le succès d'élaboration.

La portée exacte reste la vraieGamma(2+it) multipliée par la puissance complexe principale de w, Re(w)>0. L1 et les deux intégrands signés sont construits depuis Local26 et Laplace. Pour H≥0, la négation préservant Lebesgue transporte la queue négative vers Iio(-H) ; la séparation de [-H,H] construit l'identité entre l'erreur de troncature de `complexGammaInverse` et la somme des deux queues. Chaque norme≤C exp(-δH)/δ ; la normalisation1/(2π) et l'inégalité triangulaire donnent exactement `R=C exp(-δH)/(πδ)`, avec C=|w|^(-2)sec²η, η=(π/2+|Arg(w)|)/2, δ=(π/2−|Arg(w)|)/2>0. Aucune annulation des signes n'est supposée.

La continuité jointe démontrée dans la SOURCE est celle du rayon fermé R, pour Re(w)>0 et H réel quelconque. Elle ne prouve pas seule la continuité jointe de l'intégrale mobile. La boule du dernier théorème dépend de H fixé ; pour T≥H elle contrôle la queue par2R(w,H), sans fournir une boule indépendante de H à l'infini. La limite Lean H→∞, la convergence locale uniforme et le raccord exp(-w) via Hol27 restent absents et explicitement ouverts dans le contrat.

Local26 est le seul import local direct : vraie ligne PASS22, sourcee54cac5b…/olean364ac79a… ; reçu globalFAILED53201e46… et observation ROOTpartial9b7697d2… restent intacts. Gamma02 et Thermal20 sont ses dépendances transitives readonly. Aucun crédit de l'ancien Hol02 échoué ou d'un calcul numérique n'est repris. FAIL28 exact reste archivé :log9f97625c6e08c35f5d06eef3c152b6588db84b315fb9616c67541fe3307cb7e0, reçu3d724ee2096e676738e55c33c65a36909418930b4a0e40c0a0d7086ad38c06da,22prints dont7sorryAx de récupération et aucun olean.

Le futur lot29 peut être limité à ce module22 et ses trois dépendances readonly ; ses outils SOURCE n'autorisent aucun PREP ou Lean. La fermeture d'import et une gate ROOT distincte demeurent nécessaires. Aucun facteurζ, échangeΛ, zéro spectral, correction PP, coefficientN=10^8, nouveau signe canonique, D_N ou WIN n'est payé.
