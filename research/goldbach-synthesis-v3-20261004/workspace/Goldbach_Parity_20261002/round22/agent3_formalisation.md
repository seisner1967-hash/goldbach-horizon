# ROLE3 — formalisation effective de G0

Le pivot est géométrique. Les noyaux et leurs intégrales sont définis avant leurs formules, avec positivité, dérivabilité, convergence et intégrabilité prouvées. Aucune forme bilinéaire arithmétique, crible, inversion de Möbius, Vaughan ou reste scalaire de progression n’est utilisé.

État final auteur au2026-10-03T08:42:32UTC : Kernel revision02, Finite revision03, Unfold revision04 et Tail stage04 ont compilé réellement avec Lean4.15, une invocation autorisée pour chacun de ces sources finales, exit0 et respectivement33,18,19 et14audits standards. Leurs sources et olean sont immuables. Les échecs précédents restent conservés. L’infini et la queue continue jointe sont désormais prouvés en auteur. Les quatre modules comportent69théorèmes,15définitions et84audits qualifiés. Le banc G0 réel24cas a été accepté par root comme AUX ; il n’a pas été rejoué parROLE3. Le crédit officiel reste au Juge indépendant/root.

## Sorties Lean conservées

| Étape | Sortie réelle | Diagnostic exact |
|---|---|---|
| Kernel attempt01 | exit1, sans olean,07:02:03–07:02:31UTC | Normalisations de négation/division ; buts numériques après convert ; fermeture prématurée de tactiques ; rationalisation du déficit sans son identité factorisée. |
| Kernel attempt02 | exit0,07:14:47–07:15:17UTC | Primitive, FTC, limites, intégrabilité de la droite, intégrale complète et déficit effectivement compilés ;33audits exclusivement propext,Classical.choice,Quot.sound. |
| Finite attempt01 | exit1, sans olean,07:21:53–07:22:16UTC | Continuous.const_mul absent ; extrémités m+n/n+m dans l’algèbre affine ; simplification Int.negSucc incomplète. |
| Finite attempt02 | exit1, sans olean,07:29:48–07:30:11UTC | Continuité et affine corrigées ; une conversion natAbs restante, transformée trop tôt en valeur absolue par simp. |
| Finite attempt03 | exit0,07:35:44–07:36:07UTC | Conversion constructive des entiers opposés ;18audits exclusivement standards, olean679f572be0d81f8c86bfa418fb460d5168774fc56b2b2537a9469ff0aca7a544. |
| Unfold attempt01 | exit1, sans olean,07:50:58–07:51:23UTC | Réécriture rpow_natCast déjà effectuée ; égalité abs(m)²=m² non explicitée ; cast réel de negSucc non définitionnel. DCT et intégrale périodisée unitaire élaborés avec audits standards. |
| Unfold attempt02 | exit1, sans olean,07:57:27–07:57:53UTC | Exposant3 encore à convertir explicitement entre rpow réel et pow nat ; simp du carré absolu prématuré. Cast negSucc désormais élaboré avec audit standard. |
| Unfold attempt03 | exit1, sans olean,08:05:00–08:05:26UTC | Correspondance de rpow_natCast encore non trouvée par réécriture ; carré absolu et negSucc corrigés. Révision04 remplace ce cycle par des identités explicitement typées. |
| Unfold attempt04 | exit0,08:29:04–08:29:29UTC | Pont explicite entre rpow réel et cube naturel ; convergence, échange infini, périodisation et jacobien signés compilés ;19audits exclusivement standards, oleanb3e0d60e7633cc46e2084c0131e2fd42aef0f1fca60d4db7682d45ece1774bc0. |
| Tail attempt01 | exit0,08:35:09–08:35:31UTC | Déficits, vraie erreur, borne fermée et continuité jointe compilés ;14audits exclusivement standards, oleand6ca888b83bbd4644152da951df39b7712a2735ae10e233b84ea1dcb9584b025. |

Les copiesPREEXEC, START, commandes, logs, exits, POSTEXEC et reçus de chaque invocation restent immuables. Les mentions sorryAx dans les logs d’élaboration échouée ne sont ni des placeholders source ni une preuve acceptée. Ces erreurs techniques ne réfutent pas une identité analytique et ne constituent pas une obstruction de parité.

## Sources concrètes

Kernel : K_a(u)=1/((u²+a²)√(u²+a²)), H_a(u)=u/√(u²+a²), P_a=H_a/a². Pour a>0, P_a'=K_a, K_a est intégrable surℝ et son intégrale vaut2/a². Le déficit1−H_a(u) est rationalisé exactement et borné pouru>0.

Finite : l’intégrale de la fenêtre n∈[−Q,Q] du noyau original y^(3/2)/(((mx+n)²+(my)²)^(3/2)) est calculée par substitution affine signée. Le télescopage conserve q=natAbs m cellules aux deux bords Q+1..Q+q et−Q..−Q+q−1. Le signe m<0 est payé par la bijection n→−n de la fenêtre.

Infini compilé en auteur : un majorant local sommable, constitué d’une fenêtre finie et8|n|^-3, donne convergence et continuité de la périodisation. La sommabilité des intégrales des normes vient du partitionnement en cellules et de l’intégrabilité réelle. Le nombre de recouvrements signé m est traité par périodicité exacte, avec jacobien m^-1. La formule effectivement prouvée est2/(|m|²√y), avec y>0 et m≠0. Source SHA79384d3502ab8042b44104e0ba4e56087c47430c267c2b9f16f9c6f228426aea ; log SHA12cc50cc686994a04af46290727ed38de7e11eaf09622c67d5fcfb1544c63060, FULL4ee808 ; reçu FULL289c04.

Queue compilée en auteur : l’erreur réelle entre intégrale infinie et fenêtre finie est exprimée par la somme des déficits aux deux bords. Chaque coordonnée positive est au moinsQ−q. Les déficits sont positifs, leur somme≤q a²/(Q−q)², et le prefacteur donne exactement y^(3/2)/(Q−q)². L’enveloppe est continue en y pour Q,q fixés ; sa version réelle est continue conjointement en (y,T) sur T>q. La gardeQ>q figure dans l’énoncé. Source SHA5f9d3f180df2e165d43aebfe2e72b963091bb2b90fdfa4e786a66cc82745af8e,11théorèmes+3définitions+14audits ; logaf4334b90177fa791f1ee4cd1befd21c2039c70db2a08dbbd32b02663cce535d, FULL4cc683 ; reçuFULL2811c0,30inputs inchangés, invocationunique0db819/session95994 finalf59e90 exit0.

ROLE4 a relu la queue FULLa30387 et l’infini FULLfdffac avec des API locales ciblées ; aucune charge mathématique manquante n’a été signalée. Cette relecture SOURCE n’est pas un résultat du compilateur.

Le raccord G0_raccord_final.md et le catalogue final G0_final_catalog_v2.json sont gelés. La préparation metadata v1 a laissé deux totaux à null par l’usage de Measure-Object sur OrderedDictionary ; elle est conservée intacte. Une réparation metadata distincte, réelle41d11d exit0, somme explicitement les comptes vérifiés de chaque module :69théorèmes,15définitions,84audits. Cette réparation n’a lancé aucun Lean ou Python math. Catalogue final SHA8d799d5742b7d674cd5a5e184126cba3fcfcc59808af8facb1b30b5ee18ba9c0, FULL3a7358 ; reçuFULL886fff.

## Portée

G0 reste un auxiliaire géométrique. L’assemblage cusp0, la diffusion, les liens avec les premiers/zéros, Mellin, chaleur, coefficientN et majoration de D_N ne sont pas crédités par ces sources. Aucun résultat au testN=10^8 n’est confondu avec la garde sourceu=logN≥10^24. Les comptes officiels relèvent de la validation indépendante du Juge et de root. Aucune victoire n’est revendiquée.
