# ψ04 : P1 auteur compilée ; duplication refusée

La tentative réelle unique 74b7ae, session50930, s'est terminée 5af46d exit1.
Les trois logs et le reçu ont été lus FULL e0ad4a. Beta23 puis Integral10 sont
AUTHOR_LEAN_AUX_PASS avec tous leurs noms exacts et axiomes standards ; le
parseur wholetext a effectivement lu aussi les listes imprimées en plusieurs
lignes. Le transport exp(-u), sa véritable intégrabilité et P1 sont compilés.
Le champ global P1_author_source_compiled du launcher était conservativement
lié au succès des trois modules : il vaut false puisque Duplication a échoué.
Les lignes détaillées du reçu établissent les deux PASS réellement distincts.
Un audit indépendant du Juge demeure nécessaire pour leur crédit officiel.

Beta START11:21:53.355382 FIN11:22:28.182159UTC, source b4adf3ac…,
olean28e54d352bde19a6ab175dfa6dfa7667f41e2f644b81c90ac6256ead16b40cd0.
Integral START11:22:28.182159 FIN11:22:44.378018UTC, source3f254cdf…,
olean5dd15ee927c32894e7cafb4f05c78fb65c48e1cca93d91eee7ae96518f43ee1e.
Core03, Beta04 et Integral04 sont readonly et ne sont pas recompilés.

Duplication START11:22:44.393634 FIN11:22:58.645746UTC exit1 sans olean,
log4d6056cff6d751980700d7cbede7ef910ce65c16bb2fa3eb929ae4afb0077f43.
Quatre erreurs précises :25 et52 la simplification natCast ne réduit pas les
numéraux OfNat, laissant Complex.re2/im2 dans le signe ;41 des fonctions
composées et id restent sous Gamma/cpow dans l'identité dérivée ;65 le
field_simp sur des expressions imbriquées normalise z+1/2 en 1/2+z et laisse
des inverses Gamma qui ne peuvent être annulés par ring seul.

Réparation SOURCE distincte : payer les deux projections du numéral2 par rfl,
réduire Function.comp_apply/id_eq avant l'algèbre de la dérivée, et former le
dénominateur commun par le vrai div_add_div au lieu de field_simp récursif.
Le quotient véritable Gamma, toutes conditions de non-annulation et la
différentiation de Legendre restent présentes. Aucun axiome cible ajouté.
Les sorryAx du log résultent de l'élaboration échouée et ne sont jamais
acceptés. Il s'agit de tactiques/API, pas d'une réfutation analytique/parité.

Reçu73580f763b089606dbe488720d86920658dacad1b100657c26b9c8cc2cf4209b.
POSTf214a520de3d5ede226df9932c25e28106612db45c3a371ab905481bc31ddcaf
parsé pour intégrité74inputs/6476cache inchangés ; aucune lecture FULL humaine
du PRE/POST volumineux prétendue. La gate04 est consommée. Duplication seule
attendra une préparation et une nouvelle gate. C5/H1 global/D_N/WIN ouverts.
