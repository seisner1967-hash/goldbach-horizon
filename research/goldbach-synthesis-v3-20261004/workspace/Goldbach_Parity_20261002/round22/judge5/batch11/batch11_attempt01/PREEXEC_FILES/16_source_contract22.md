# Projection — enveloppe SOURCE autonome

`ThermalProjectionEnvelope22.lean` contient 42 déclarations et leurs 42 audits qualifiés. Statut : SOURCE uniquement, sans compilation, calcul numérique, préparation d'exécution ni crédit officiel. Les imports sont mathlib; aucune dépendance C5 non compilée n'est employée.

Le module définit la vraie trace \(\mathcal T_a(\theta)=\sum_{n\ge0}\Lambda(n)r^ne^{in\theta}\), \(r=e^{-a}\), et sa somme finie jusqu'à M. Le terme n=0 vaut zéro. La borne \(\Lambda(n)\le n\) est dérivée directement de la définition sur les puissances premières, de \(\minFac(n)\le n\) et de \(\log x\le x-1\); aucun majorant arithmétique n'est fourni en prémisse.

Pour \(a>0\), les vrais résultats HasSum des séries géométriques paient

\[
A(a)=\frac r{(1-r)^2},\qquad
B(a,M)=r^{M+1}\left(\frac{M+1}{1-r}+A(a)\right).
\]

La somme décalée contient exactement les indices k+(M+1). La comparaison des normes construit la convergence absolue, les bornes uniformes A et B et la continuité en θ. L'identité somme finie+queue=somme entière est utilisée pour l'erreur de trace. L'involution θ→−θ, la conjugaison et l'inégalité triangulaire donnent la vraie erreur de corrélation \(2AB\). La continuité construit l'intégrabilité des deux integrands sur [0,2π]; la norme du caractère vaut1. Leurs deux intégrales, normalisées exactement par \(e^{aN}/(2\pi)\), satisfont alors dans la SOURCE

\[
\lVert\mathcal P_{a,N}-\mathcal P^{(M)}_{a,N}\rVert
\le E(a,N,M)=2e^{aN}A(a)B(a,M).
\]

La positivité et la continuité fermée de A, B et E sur a>0 sont également dérivées, pour N,M entiers fixés. Tous les dénominateurs sont non nuls sur ce domaine. Il n'existe aucun rayon ε libre ni hypothèse d'intégrabilité finale.

Cette erreur compare deux intégrales de traces concrètes. Le théorème d'orthogonalité qui les identifie au coefficient arithmétique N n'est pas démontré dans ce module. L'alias DFT reste dans l'annexe papier précédente. L'inversion spectrale utilisant la vraie zêta, un producteur de boîtes uniforme en θ, la correction des puissances propres, la frontière canonique et la cible sur D_N demeurent ouverts. L'expression closed form n'a pas reçu de verdict Lean. Une future exécution exige une préparation et une gate ROOT distinctes.
