**Juge indépendant — boucle 15, verdict PARTIAL, score 0, victoire false.** Le contrôle en lecture seule a terminé avec code 0. Les identités et les deux réductions proposées sont utiles, mais aucune estimation indépendante ne paie la covariance pondérée, l’incidence des cibles sans parent premier ou le complément du bilan. Aucun candidat Lean quantitatif admissible n’a été soumis dans cette boucle : `lean_invoked=false`, zéro nouveau module et zéro nouvelle conclusion. Le cumul historique reste de **15 modules et 208 conclusions auxiliaires**.

Le gel est intervenu après les signaux TERMINÉ des rôles 1, 2 et 6. Le manifeste d’entrée contient 39 fichiers de production, dont les trois rapports définitifs, les scripts et leurs helpers, les gates, les snapshots, les logs et les reçus. Le manifeste numérique conserve 35 bindings. Les trois sorties isolées existantes sont comparées à leurs originaux sur tous les octets et tous les champs ; leurs statuts distincts sont conservés. Le Juge n’a exécuté aucun producteur, ancien PASS, module Lean ou rendu PDF. Son unique lancement réel, avec stdout/stderr, commande et code retour, est archivé dans `judge/audit_launch.log` et `judge/audit_launch_receipt.json`.

| Entrée | Statut conservé | Portée |
|---|---|---|
| `incidence.json` | `PASS_NEW_COMPLETE_141_MASK_PROJECTION_AND_COVARIANCE_ONLY` | Masque structurel complet d=141, projection et covariance finies ; cinq kernels D/W déclarés séparément. |
| `fusion.json` | `PASS_NEW_COMPLETE_SMALL_CORE_FUSION_UNION_AND_PRINCIPAL_MAJORANT_ONLY` | Fenêtre complète q premier unitaire entre 8000 et 8200, union des parents, vrais brackets et majorant F4. |
| `incidence_moment.json` | `PASS_NEW_READ_ONLY_INCIDENCE_L4_AND_EXACT_AP_FRONT_SUPPLEMENT` | Comparaison L4 et front AP à partir des vecteurs gelés, sans recalcul des kernels ou de l’incidence. |

L’audit vérifie 1 138 positions de signes rationnels : 1 131 certificats structurés et sept intervalles L4/AP. Il compte 951 signes négatifs, 91 positifs et 96 zéros exactement certifiés, sans flottant ni signe indéterminé. Quatre falsifiers sont confirmés dans leur portée locale ; une autre promotion porte seulement le statut `NO_COUNTEREXAMPLE_IN_WINDOW`. Il n’existe aucun essai numérique échoué dans les trois journaux canoniques de cette boucle et aucun échec Lean à enregistrer. Les corrections de domaine effectuées avant le gel du rapport 2 ne constituent pas des erreurs du compilateur.

La conservation est vérifiée indépendamment avant et après : exactement 651 fichiers, soit les 603 précédents et les 48 finaux de la boucle 14. L’inventaire réel, les ajouts et suppressions, les 47 bindings du controller14 et son propre SHA concordent. Le PDF et le ZIP originaux restent intacts. Les sorties futures, les caches, l’état Arbor et le rapport central vivant sont exclus conformément au registre, sans exclusion de champs des gates. Les rapports et sources des autres rôles n’ont pas été modifiés.

La première piste réduit correctement les images c,r,s,q à un conducteur d=cr≤a. Le masque β dépend seulement de la structure du cofacteur b=sq ; la primalité de n=N−db n’entre pas dans sa définition. La factorisation ordonnée fournit un représentant physique unique. La restriction à b unitaire est nécessaire : la densité est ρ=Mβ/J, et non Mβ divisée par le nombre entier d’éléments de l’intervalle. Pour ζ=β−ρ1_U, les égalités Σζ=0 et ||ζ||²=Mβ(1−ρ) sont exactes, avec traitement séparé du cas J=0.

Le majorant écrit Mβ≤64B/log a découle du majorant de Chebyshev exposé dans le rapport 1 et de la somme des inverses des premiers s entre √a et a. Il contrôle la taille structurelle du support, sans minorer ses incidences premières. Le centrage fournit

\[
\sum \beta\theta=\rho T+\Gamma,
\qquad
|\Gamma|^2\le M_\beta(1-\rho)
\left(\sum\theta^2-\frac{T^2}{J}\right).
\]

Ce passage est valide. La covariance Γ reste un terme à estimer, ainsi que sa comparaison avec les incidences réelles des parents de C16/C17. La petite taille de d ne transforme pas le masque β en constante sur les premiers. La borne de support et Cauchy seules ne fournissent pas la compensation signée exigée après agrégation avec les poids et les erreurs W.

Au banc N=10⁸, d=141 donne I=[7093,702127], soit 695 035 entiers et 278 014 unités. Le masque complet contient 4 201 éléments, θ_U compte 60 982 axes premiers et θ_β en compte 912. La densité vaut 4201/278014, la norme carrée 1150288413/278014 et Γ est strictement négative. Ce dernier fait réfute uniquement le remplacement **exact** β→ρ1_U. Il ne réfute ni BV ni une borne asymptotique éventuelle. La constante 64/log a dépasse 1 à ce N : le banc ne teste pas son efficacité asymptotique.

La complétude de la liste de premiers utilisée pour β est justifiée par les gardes, pas par une troncature tacite. Les inégalités 47s>3163 et 3s≤3163 donnent 68≤s≤1054. Les entiers 68, 69 et 70 sont composites ; le premier s possible est 71. Alors q≤⌊702127/71⌋=9889<10000. Le helper protégé construit tous les premiers jusqu’à isqrt(N)=10000, soit 1229 premiers, dernier 9973. Les possibles s et q et les bases des puissances propres sont donc couverts. Cette vérification ne rejoue pas le producteur d’incidence.

Le supplément L4/AP conserve Σθ² et laisse T² factorisé, sans développer une matrice quadratique dense. Ses intervalles stricts certifient la variance et le gap de Cauchy positifs. Il garde n_lo=1000093, n_hi=98999887 et X=97999795. Pour φ(141)=92,

\[
X=d(|I|-1)+1,
\qquad
\frac{X-d|I|}{\varphi(d)}=-\frac{35}{23}.
\]

Le front n’est donc pas remplacé par d|I|. Les exceptions provenant des premiers divisant N sont vides dans cet intervalle, puisque ces premiers sont 2 et 5. L’erreur AP littérale est négative au banc ; aucune constante ni seuil BV n’en est déduit.

Le raccord écrit entre l’erreur cumulative et l’erreur dyadique garde le facteur K_N et le terme 1/φ(d). La convention dyadique de θ et le maximum d’erreur sont bien ceux de la référence primaire ; sa forme qualitative ne fournit pas ici de seuil effectif supplémentaire. [Goldston, Graham, Pintz et Yıldırım, équations (1.5)–(1.7)](https://arxiv.org/pdf/math/0506067). Les conditions Type I/II de l’autre référence portent sur le poids du candidat j=vw. Le fait que d divise N−j ne vérifie pas ces conditions sur j ; ni les plages ni les erreurs requises ne sont établies pour ζ. [Ford et Maynard, sections 4.2–4.3](https://www.ford126.web.illinois.edu/wwwpapers/prime-producing-sieves.pdf).

Les cinq profils D/W sélectionnés portent sur m=40074033, 41335419, 41375463, 41758701 et 41923389. Ils gardent le vrai cap Q, R=min(Q,⌊(m−1)/a⌋), les unités, la frontière stricte, U_alpha+annulus et k=1 conjoint. Ici U_a=log3, μ(m)=+1 et C=W−log3. Ils constituent un échantillon déclaré : les 907 autres images premières de β ont leurs erreurs W littérales non évaluées et non payées. Les 49 puissances propres unitaires de l’intervalle, dont quatre dans β, restent dans le raw ; aucune restriction μ(n)² ne les supprime.

La seconde piste garde la véritable identité de cœur entier. Pour un cœur squarefree e≥2 et q>a, lorsque les courts sont exactement Div(e), U_a=−Λ(e) et

\[
C_{eq}=\Lambda(e)+\mu(eq)W_{eq}.
\]

Le cas physique e=1 reste séparé : C_q=−log q−W_q. Un cœur premier apporte aussi Λ(e)=log e. Ces branches ne peuvent pas être absorbées dans une formule composite de rang impair. Le corrigendum avant gel impose pour F2–F5 un cœur cible E de rang pair au moins 4 et des parents e composites de rang impair au moins 3. Le même domaine q doit satisfaire les gardes bulk, unités et Q pour **tous** les couples sélectionnés ; les points hors gardes restent au complément initial.

Avec ces gardes, les cibles ont C=−W et les parents C=+W. Les parents physiques sont réunis avant tout crédit. Pour E fixé,

\[
\Delta_E=\sum_q\left(I_E\log n_E-\sum_{e\in U_E}I_e\log n_e\right)
\le \sum_q I_E\log n_E\,\mathbf1_{D_q=0}.
\]

Le majorant F4 est une comparaison exacte par cas, sans existence de parent supposée. Il conduit au modèle

\[
B_E=S(N)\Delta_E+
\sum_{q,e}I_e\log n_e\,\delta_e-
\sum_q I_E\log n_E\,\delta_E.
\]

Deux obligations subsistent : l’incidence couplée F6 d’une cible première sans aucun parent premier, et les erreurs physiques δ. Fixer un petit cœur ne donne pas une progression ordinaire de premiers : q est également premier et la cible dépend du même q. Une somme sur plusieurs E doit en outre préserver l’union globale des parents ; leurs capacités ne sont pas réutilisables librement.

Le banc E=3003 vérifie tous les 21 q premiers unitaires de 8000 à 8200. Les six cofacteurs donnent 86 représentations et 78 cœurs parents distincts. Les 1680 axes physiques gardent toutes leurs incidences θ/raw. Les 416 profils D/W couvrent tous les termes non nuls et les contrôles ; les 1264 termes exactement nuls gardent des W littéraux non estimés. Le parent e=231 a trois représentations : compter les labels donnerait 400 parents premiers au lieu des 360 vertices premiers. Ce surcrédit est falsifié.

Les sept cibles premières produisent 112 arêtes. Les 248 parents premiers dont la cible est composite restent dans la somme entière. Aucune cible orpheline n’apparaît dans cette fenêtre, mais ce résultat reste `NO_COUNTEREXAMPLE_IN_WINDOW` et ne devient pas une couverture générale. La somme principale et la somme physique entière après union sont négatives. Les 112 principaux appariés sont négatifs, tandis que les paires physiques comptent 71 signes négatifs et 41 positifs : l’identification systématique principal/réel est falsifiée. Chaque arête garde le raccord exact avec les deux W ; le résultat entier n’est pas obtenu en dupliquant la cible par arête.

Le minimum 3·7·11·13·17·3164=161525364>N rejette uniquement une scission à six facteurs unitaires distincts dans ce banc. Il ne constitue pas une impossibilité asymptotique. De même, le c maximal de J2 est 9 et ses cœurs squarefree unitaires sont 1, 3 et 7 à ce N : l’absence de cofacteur composite dans ce secteur fini ne supprime aucun secteur global. Les contrôles de cœur premier, les deux signes de μ, les modèles S(bN) aux véritables indices supprimés et les poids log p/log m restent présents. L’absence finie de puissances propres dans la fenêtre de fusion ne transforme pas raw=θ en identité globale.

Le bilan reste

\[
D_N=B_{\rm prime}^{a}+B_{\rm pp}^{a}
+P_{{\rm bande},\ge2}+Z_{{\rm face},\ge2}
+I_\alpha+2\max(e,0).
\]

P5/K2 concerne J2bulk entier avant retraits. U4 et la variation sont des routes alternatives, sans double paiement NG54. Le complément conserve c=1, e=1, b=1, −S(N)N, S(bN), les cofacteurs longs, les moments J0/J1/J2 restants, les célibataires, faces, points hors bulk, les fronts et le terme couvert. Le seuil BV supplémentaire n’est pas évalué. N=10⁸ est extérieur au domaine source u=log N≥10²⁴. Les falsifications finies d’assertions exactes ne sont pas présentées comme des réfutations de futurs théorèmes limités à ce domaine.

La boucle localise ainsi deux estimations indépendantes manquantes : la covariance structure/primalité pondérée de la première route et l’incidence OR avec union globale de la seconde. Aucun paiement complet de D_N≤N/(256 log N log log N) n’est démontré. Le verdict sémantique reste **PARTIAL, score 0, victoire false** ; l’objectif de recherche reste actif.

La commande B_dev reproductible est `& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round15\judge\audit-judge.ps1'`. Le manifeste d’entrée a SHA `2e107ea84ee1403550e3a60c4b9a8bab54a65fca434e4c36ce073a4673b76be3` ; le reçu du Juge `e679efb162c6eed5c93675b38af648e9796c7b92aa06be62b2d8edfd52645bab` ; le stdout réel `332069762a68fa3bd9917c0d951661d97300b38317d29c38d06eb66a7252d82b`. Le reçu de lancement lie ces empreintes à l’exécution exit 0. Aucune réexécution après validation n’a été nécessaire.
