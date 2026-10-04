# Géométrie liée du noyau Gamma sur le cercle — SOURCE25 seulement

[ComplexGammaCircleGeometry22.lean](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_circle_geometry_source01/ComplexGammaCircleGeometry22.lean) est un nouveau module de **25 déclarations : 22 théorèmes, trois définitions et25 impressions qualifiées**. Il n'a été ni compilé, ni probé, ni préparé pour exécution. Le catalogue est manuel, fondé sur les lectures FULL de la source, sans parser candidat. Toutes les anciennes sources gelées sont conservées.

L'unique import local est `ComplexGammaMellinLocal22`, dont la ligne Local du vrai lot26 est indépendamment PASS22 et observée ROOT. Le reçu global26 demeure FAILED ; ce statut global n'est pas transformé en PASS. Ses imports transitifs GammaPrerequisites et ThermalGammaMellinInverse sont les binaires readonly déjà acquis, sans nouvelle compilation demandée. Ni Lambda30, ni EΛ16, ni Tail, ni une formule ζ n'est importé. Cette SOURCE est autonome par rapport à l'échange arithmétique encore en attente.

## Objets et domaines

Le point réel de phase est w(a,θ)=a−iθ ; son rayon est r(a,θ)=√(a²+θ²). Ce sont les vraies fonctions `circleMellinPoint` et `circleMellinRadius`. Pour a>0 et θ réel quelconque, la source construit Re(w)=a, Im(w)=−θ, w≠0, w∈slitPlane et r=‖w‖>0. Aucune condition d'appartenance finale n'est donnée en hypothèse.

Les fonctions actualLocal26 sont

\[
\eta(w)=(\pi/2+|\operatorname{Arg}w|)/2,\quad
\delta(w)=\eta(w)-|\operatorname{Arg}w|,\quad
C(w)=\|w\|^{-2}\left(1/\cos\eta(w)\right)^2.
\]

La SOURCE géométrique écrit l'identification de la vraie branche :

\[
\operatorname{Arg}(a-i\theta)=-\arctan(\theta/a),\qquad
|\operatorname{Arg}(a-i\theta)|=\arctan(|\theta|/a).
\]

`Complex.abs_arg_lt_pi_div_two_iff` place l'argument dans l'intervalle d'inversion de la tangente. `Complex.tan_arg`, puis `Real.arctan_tan`, identifient l'argument ; l'imparité d'arctan et ses signes sont payés séparément. On ne substitue pas un argument arbitraire modulo2π.

## Identité serrée et sa borne

Les deux branches de signe de θ paient
sin|Arg(w)|=|θ|/r. L'identité `Real.cos_two_mul`, avec 2η=|Arg(w)|+π/2, donne

\[
\cos^2\eta=\frac{r-|\theta|}{2r}.
\]

Le carré de la norme vaut r²=a²+θ². En multipliant la précédente identité par r+|θ|, la preuve construit réellement
2r cos²η(r+|θ|)=a². Les dénominateurs de C sont non nuls : a>0, r>0, η∈(0,π/2) donnent cosη>0. `Real.rpow_neg` et `Real.rpow_two` convertissent le rpow négatif en inverse du carré, puis l'égalité polynomiale paie

\[
C(a-i\theta)=\frac2{a^2}\left(1+\frac{|\theta|}{r}\right)
=\frac2{a^2}\left(1+\frac{|\theta|}{\sqrt{a^2+\theta^2}}\right).
\tag{CG}
\]

La vraie inégalité |Im(w)|≤‖w‖ donne |θ|/r≤1 ; comme2/a²≥0,

\[
C(a-i\theta)\le\frac4{a^2},\qquad a>0,\quad\theta\in\mathbb R.
\tag{CB}
\]

La source ne fournit ni formule(CG), ni majorant(CB) en prémisse. Elle conserve la relation entre rayon et argument, qui était perdue dans le majorant compact séparé. L'égalité fine du maximum C̄ à |θ|=π et la monotonie en |θ| de la fraction liée ne sont pas des théorèmes de ce paquet : elles restent des raccords PAPER de la note de faisabilité.

## Minorant positif de décroissance

La troisième définition est d(a)=atan(a/π)/2. Sa positivité pour a>0 est construite par la stricte monotonie d'arctan et π>0. La source écrit aussi

\[
\delta(a-i\theta)=\frac{\pi/2-\arctan(|\theta|/a)}2.
\]

Si |θ|≤π, la monotonie d'arctan compare |θ|/a à π/a. Le vrai théorème `Real.arctan_inv_of_pos`, appliqué à π/a>0, donne atan(a/π)=π/2−atan(π/a), inverse/division normalisés par `inv_div`. La preuve conclut

\[
\delta(a-i\theta)\ge d(a)=\tfrac12\arctan(a/\pi)>0,
\qquad a>0,\ |\theta|\le\pi.
\tag{DG}
\]

Ainsi le minorant demandé est inclus, sans identité finale ni floor arbitraire offert en hypothèse. Il n'y a pas de dette mathématique implicite sur ce minorant ; l'élaboration future reste à vérifier par le Juge.

## Continuité, limites et vérification future

La SOURCE écrit la continuité globale du rayon r surℝ², de d surℝ, et la continuité au point p.1>0 du membre fermé de(CG), avec ses deux dénominateurs payés. Elle ne contient pas encore un théorème de continuité du coefficient intégral, un transport de somme/intégrale ou un reste de quadrature. La continuité de l'objet actual C sur le demi-plan de paramètres peut être raccordée à cette égalité locale ; aucun nouveau théorème de cette dernière composition n'est compté ici.

Les signatures ont été réellement lues TARGETED dans le cache mathlib4.15 : Arg/tan/sin, arctan_tan/neg/monotonie/inverse/continuité, double-angle/cos_add_pi_div_two, norme/abs, rpow négatif, ordre de division et génération additive de norm_pos_iff. Le cache n'est pas annoncé FULL. Les risques résiduels sont techniques d'élaboration : typage des arguments implicites, réduction des définitions locales et normalisation rationnelle/polynomiale après field_simp. Aucun probe n'a testé ces tactiques.

La [note PAPER de faisabilité](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/mellin_lambda_feasibility_paper01/feasibility22.md) et son handoff restent byte-identiques. Ses estimations de hauteur, coûts et autres budgets ne sont pas promues par cette SOURCE non compilée. Aucun coefficient àN=10^8, aucune formule globale ζ, annulation signée, correction PP/front, borne de D_N ou WIN n'est obtenu. Une revue indépendante puis une sélection/gate ROOT distincte sont nécessaires avant tout compiler futur ; cette livraison ne demande aucune exécution.
