# Réparation SOURCE des trois raccords Tail28

Un module SOURCE distinct, `ComplexGammaMellinTail22.lean`, conserve les 22 déclarations, les domaines, les définitions et les 22 impressions qualifiées du paquet01. Aucun compilateur, probe, candidat importé ou calcul numérique n'a été exécuté par l'auteur. La baseline ROOT27 reste 85 modules/1434 déclarations ; aucun crédit Tail n'est ajouté.

Le vrai lot28 s'est terminé exit1 : START 2026-10-03T23:54:17.724277UTC, FIN 23:54:52.190834UTC. Le reçu est `3d724ee2096e676738e55c33c65a36909418930b4a0e40c0a0d7086ad38c06da`, le FIN `f426a2c77b5c2614751a554ba28de7022f376ed48626678e0c1cf004b367ec89` et le log `9f97625c6e08c35f5d06eef3c152b6588db84b315fb9616c67541fe3307cb7e0`. Ils sont lus FULL et restent immuables. Les 9 diagnostics concernent trois sites et leurs cascades ; le module ne produit pas d'olean. Ses 22 impressions comptent 15 standards et 7 récupérations sorryAx. Ces récupérations viennent de l'élaboration échouée ; la SOURCE n'introduit pas un sorry ou un axiome. Aucun contre-exemple analytique ou blocage de parité n'est établi par ce log.

Trois changements seulement sont apportés aux preuves, dans le sibling02 :

1. L'expression `(h0.const_mul C).mono_set` avait été réduite au type `Integrable` sur une mesure restreinte, empêchant la recherche du champ `IntegrableOn.mono_set`. Une variable `hmul : IntegrableOn (fun t => C*exp(-d*t)) (Ioi 0)` rend le domaine explicite, puis l'appel qualifié `IntegrableOn.mono_set hmul (Ioi_subset_Ioi hH)` paie la restriction. L'API réelle est `MeasureTheory/Integral/IntegrableOn.lean:103–104`.
2. `integral_add_compl` ne pouvait pas inférer les deux bornes du `measurableSet_Icc` fourni. L'appel reçoit désormais `(s := Icc (-H) H)`, avec f et volume toujours explicites. L'API réelle `SetIntegral.lean:178–180` attend précisément cet ensemble et L1 du vrai noyau, déjà construit dans Local26.
3. La composition de continuité avait inféré la section `H↦(w,H)` au lieu de `z↦(z,H)`. La preuve construit explicitement `hp : ContinuousAt (fun z : ℂ => (z,H)) w`, avec fonctions et point annotés, puis compose la continuité jointe du rayon à hp et réduit `Function.comp_apply`. Aucun rayon ni continuité finale n'est ajouté comme prémisse.

Les hypothèses mathématiques sont donc inchangées : Re(w)>0, H≥0 pour la vraie identité de queue et son erreur ; Re(w)>0 et H réel quelconque pour la continuité jointe du rayon fermé. Chaque queue signée est construite depuis le Laplace réel et la vraie domination Gamma de Local26. La négation est transportée par le volume de Lebesgue ; les deux demi-droites du complément de [-H,H] sont disjointes. La normalisation finale reste exactement

`R(w,H)=|w|^(-2)sec²η(w) exp(-δ(w)H)/(πδ(w))`,

`η=(π/2+|Arg(w)|)/2`, `δ=(π/2−|Arg(w)|)/2>0`.

La continuité de l'intégrale complexe à seuil mobile et un théorème de convergence H→∞ ne sont pas ajoutés. La section locale uniforme existe pour un seuil H fixé, pas comme un rayon numérique fourni. Le module continue de conclure sur `complexGammaInverse`, sans importer Holo27 ou offrir l'identité avec exp(-w). Ce dernier raccord appartient au brouillon distinct Λ–Mellin, qui demeure non gelé et non compilé.

La seule dépendance locale directe est le vrai Local26 PASS22 : SOURCE e54cac5b…, olean364ac79a…, reçu global26 FAILED53201e46… dont la ligne Local seule PASS est observée par ROOT9b7697d2…. Les dépendances transitives Gamma02 et Thermal20 restent readonly. Aucune recompilation d'acquis n'est demandée par ce handoff. Le paquet source01/lot28, la revue indépendante SOURCE01 et les 3089 archives sont conservés ; la nouvelle fermeture est une liaison SOURCE/API par octets, pas une fermeture d'imports/PREP.

Une nouvelle revue indépendante puis une sélection/gate ROOT sont nécessaires avant toute compilation de cette réparation. H1, échange global spectral de ζ, corrections PP/front, coefficient numérique N=10^8, D_N et WIN restent ouverts. La tentative numérique05 séparée n'est pas utilisée comme preuve ou entrée de ce module.
