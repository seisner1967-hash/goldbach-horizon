# ROLE2/22 — contrat Lean proposé, non exécuté

Statut : PAPER_CONTRACT / NO_LEAN_SOURCE_COMPILED. Ce contrat propose des objets et obligations concrètes ; il ne les transforme pas en axiomes ou hypothèses de victoire. Aucun fichier Lean comportant des placeholders n'est livré pour donner une impression de preuve. Toute déclaration explicite ultérieure recevra un `#print axioms` qualifié. Interdits : sorry, admit, nouvel axiom, unsafe, native_decide, trustMe, import de PASS ancien reconstruit ou boucle cachée de compilation.

Le premier objet formalisable est un **déroulement géométrique à poids réel**, pas encore un théorème de diffusion sur un quotient orbifold. Noms suggérés, non déclarés : `Epstein22.kernel`, `Epstein22.finiteShiftIntegral`, `Epstein22.endpointSum`, `Epstein22.unfoldFullRealThreeHalves`, `Epstein22.finiteShiftTail`. Ces noms appartiendront au namespace **Epstein22** et à des sources22 nouvellement sélectionnées.

## G0 — déroulement exact concret, premier AUX

Entrées : y:ℝ avec0<y, m:ℤ avec m≠0, q=|m| comme naturel positif, Q:ℕ avecq<Q. Domaine réel x∈[0,1], u∈R. Définir a=q y>0 et

K_m,y(x,n)=y^(3/2)/(((m:ℝ)x+n)^2+((m:ℝ)y)^2)^(3/2).

Les rpow sont réels sur des bases positives ; prouver ces bases et toutes les gardes avant dérivation/inversion. Poser H_a(u)=u/sqrt(u²+a²). Montrer par dérivée réelle que H'_a(u)=a²/(u²+a²)^(3/2). FTC exige continuité/dérivabilité et intégrabilité sur chaque intervalle réel ; leur preuve ne sera pas cachée dans une prémisse abstraite.

But fini : pour q>0,

I_Q=∫_0^1 Σ_(n=−Q)^Q K_q,y(x,n)dx
   = y^(3/2)/(q a²) [Σ_(u=Q+1)^(Q+q) H_a(u) −Σ_(u=−Q)^(−Q+q−1) H_a(u)].

Le télescope fini doit être prouvé sur `Finset.Icc` d'entiers, avec toutes les extrémités et q>1. Pour m<0, utiliser n↦−n dans la fenêtre symétrique avant simplification et prouver I_m=I_|m|. Ne pas supposer la symétrie à partir d'une valeur calculée.

But infini : intégrabilité du noyau, sommabilité uniforme suffisante pour l'échange somme/intégrale, recouvrement des intervalles [n,n+q] de multiplicitéq presque partout, puis

∫_0^1 Σ_(n∈Z) K_m,y(x,n)dx = 2/(q²sqrt(y)).

La preuve peut employer soit recouvrement continu, soit limite des sommes finies d'extrémités ; le second choix fournit directement l'objet entier concret et sa queue. La queue positive doit satisfaire

0≤2/(q²sqrt(y))−I_Q≤ y^(3/2)/(Q−q)².

Dérivation : |mx+n|≥|n|−q pourx∈[0,1]. Les deux côtés |n|>Q sont majorés par2y^(3/2)Σ_(n≥Q+1)(n−q)^−3 ≤2y^(3/2)∫_(Q−q)^∞u^−3du. Les gardes Q>q garantissent l'intégrale. Pas de capacité, moment ou petitesse deD_N en prémisse.

Obligations modes : prouver séparément le facteur1/2 de la somme de réseau, m=0 avec n≠0, et le couplage m/−m. G0 seul ne démontre ni le mode0 COMPLET à s complexe ni la géométrie de diffusion. Un PASS G0 est **UNFOLD_AUX**.

## G1 — vrai mode constant complexe Epstein

Objets : E_full surZ²\{0}, y>0, Re(s)>1, puissances `Complex.exp(s*Real.log(base))`. Montrer convergence locale uniforme de la somme du réseau et de ses dérivées nécessaires, invariancePSL2Z par bijection entière, puis équation ΔE=s(1−s)E. Pour le mode constant, somme m=0 et déroulement de chaque m≠0, Fubini absolu, intégrale beta/gamma avec Re(s)>1/2 et branches explicites.

But : C0E_full=ζ(2s)y^s+√πΓ(s−1/2)/Γ(s)ζ(2s−1)y^(1−s). Normaliser ensuite parζ(2s) ; pour Re(s)>1, non-annulation doit être dérivée, par exemple de |ζ(2s)−1|≤3/4. Ne jamais développer1/ζ en série de Möbius et ne pas utiliser la preuve divisorielle de la proposition2.5 Cakoni–Chanillo.

## O1 — identification opérateur, obligation ouverte distincte

Construire L² du quotient orbifold avecdA=y^−2dxdy, le domaine dense C∞ compact, la forme positive sesquilinéaireq, sa fermeture et le représentant auto-adjoint de Friedrichs. Définir son domaine par l'identité de forme, pas par l'énoncé «Δ auto-adjoint» en prémisse. Démontrer densité, closabilité et unicité du représentant.

Construire le cusp et l'espace de données d'onde constante. Prouver que leE normalisé appartient à l'espace de solutions admissibles ; établir existence et unicité en utilisant la résolvante hors[0,∞) et contrôler que la différence de deux solutions est réellementL² dans le domaine correct. Seulement alors identifier φ=√πΓ(s−1/2)ζ(2s−1)/(Γ(s)ζ(2s)) comme coefficient de diffusion de cet opérateur.

Les sources primaires historiques sont des obligations à formaliser, pas un axiom ajouté au projet. Aucun théorème de scattering, Weil ou Birman–Krein prêt dans ce cache n'est présumé. Une API générale éventuellement trouvée plus tard exige une lecture et un audit de ses hypothèses. Le canal de dimension1 n'autorise pas une trace Fredholm duΔ complet. Le continuum, modes constants/cuspidaux/résiduels ne sont pas supprimés.

## A1 — télescope global et Mellin, obligations indépendantes

Définir L etψ par dérivées réelles/complexes correctement choisies, φ explicite identifié enO1, D(w) pourRe(w)≥2. Montrer dérivabilité et non-annulation réelle de chaque facteur, puis D(w)=L(w)−L(w+1) et le télescope fini. La conséquence arithmétique utilise la série globale L(w)=ΣΛ(n)n^−w ; aucun estimateur deΛ n'est admis librement.

Lecture ciblée réelle du cache `Mathlib/NumberTheory/LSeries/Dirichlet.lean`, lignes325–421 : `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, `LSeriesSummable_vonMangoldt` et `riemannZeta_ne_zero_of_one_lt_re` sont publics. **Provenance de méthode** : cette preuve existante utilise la convolution classiqueΛ*1=log pour établir l'identité analytique, pas un nouveau crible ou une inversion Möbius affichée. La directive interdit de reprendre une recherche locale de facteurs ; l'import de ce résultat standard devra être explicitement audité parroot. Si cet import ne convient pas à la directive, une preuve globale analytique par produit d'Euler/dérivation uniforme est une obligation supplémentaire ; aucune convolution ne sera redérivée comme méthode candidate.

La seule série arithmétique sert à identifier le signal global, conserve tous les entiers et puissances premières. Démontrer Λ≤log, puis C(σ) par intégrale décroissante, et |F−P_K|≤C(K), K≥2. Cela ne constitue ni une nouvelle inversion ni une estimation scalaireAP.

Lecture FULL réelle du cache `Mathlib/Analysis/MellinInversion.lean` : `mellin_inversion` exige `MellinConvergent`, `VerticalIntegrable` et `ContinuousAt`, avecx>0. Prouver ces hypothèses pour le signal réel ; l'extension au demi-plan complexeRe(t)>0 nécessite holomorphie/dominance ou un calcul direct Mellin absolument convergent, qui n'est pas fourni gratuitement par cette API positive réelle.

## A2 — Poisson, Schwartz et enveloppes uniformes

Lecture FULL réelle `Mathlib/Analysis/Fourier/PoissonSummation.lean` : `SchwartzMap.tsum_eq_tsum_fourierIntegral` disponible. Les versions `Real.tsum_eq_tsum_fourierIntegral...` exigent aussi de vraies conditions de sommabilité/décroissance. Prouver la convention2π et la mise à l'échelleh, puis appliquer le théorème à v↦e^(2v)P_K(te^v).

Schwartz n'est pas un label supposé. Pour chaque ordre r, dériver la somme sous convergence dominée : la dérivée a une somme finie de termes e^(2v)(nt e^v)^a e^(−nt e^v),0≤a≤r, coefficients calculés par récursion. Au bord v→−∞, Λ≤2sqrt(n) et une comparaison intégrale deΣn^(a+1/2)e^(−nηe^v) donnent un majorant explicite C_r,η,t(e^(v/2)+e^v). Au bord v→+∞, une extractione^(−ηe^v) fournit une décroissance plus rapide que toute puissance de v. Pour chaque r et chaque poids polynomial de v, établir le supremum fini et toutes les gardes réelles. Les constantes C_r ne sont pas une estimation deD_N ; elles doivent provenir de la récursion et d'intégrales gamma/factorielles.

Démontrer ensuite l'identité de Poisson de uniform_formula, les deux signes d'alias, les gardes ηe^(2π/h)≥4(2π/h),2π/h≥log2, les queues E_T et E_J incluantJ+1 et h³. Justifier le majorant gamma exact par récurrence/reflection ou APIs publiques auditées, pas par une asymptotique sans constante. Toutes les fonctions enveloppes sont continues dans leurs domaines avec dénominateurs positifs prouvés.

## A3 — coefficient N, PP et pontD_N

Définir G_N réel avecΣ1≤n<NΛ(n)Λ(N−n). Démontrer l'extraction de coefficient sur le cercle à rayonexp(−η), produit de séries absolument convergentes et orthogonalité. PourM>N, dériver la liste exacte des alias N+lM,l≥1, l'enveloppe cubique et le rayon e^(ηN)(2B_Fε_F+ε_F²). Pas de FFT déclarée sans alias. Le contratN10^8 est celui du fichier numeric_contract, pas une garde source logN≥10^24.

Définir Q(n)=Λ(n)−log(n)1prime(n) et prouver l'expansion des trois chargesQ·prime,prime·Q,Q·Q ; ne pas les fusionner en erreur spectrale. Le raccordG_N→résiduD_N, prix physique/modèle, fronts et ledger est **OPEN**. Aucun théorème bornantD_N ou sa positivité n'est ajouté en hypothèse pour faire passerA3.

## Discipline d'exécution future

Root sélectionne après gel et conservation. ROLE6 produit un banc source-only neuf, root lit FULL les sources/rayons et donne une autorisation math nouvelle, puis seulement les formaliseurs développent/exécutent selon leur ownership et les portes. Avant chaque invocation : source figée, commande, PREEXEC, log, exit, reçu. Corriger après un FAIL réel documenté ; ne pas inventer un blocage du compilateur en phase papier et ne pas recompiler un PASS inchangé. Juge indépendant des auteurs, verdictAUX distinct deWIN. Ce document n'ouvre aucune porte d'exécution.
