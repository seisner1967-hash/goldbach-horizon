# Obligation additive distincte — identité de projection proposée

Statut : dérivation papier exacte à formaliser; aucune compilation, aucun calcul ni victoire. Cette annexe ne modifie ni le bilan canonique, ni \(\alpha\), ni les puissances premières et unités des acquis. Elle expose ce que l'identité thermique monovariable ne paie pas encore.

Pour \(a>0\), soit le champ de trace continu périodique

\[
\mathcal T_a(\theta)=\sum_{n\ge1}\Lambda(n)e^{-an}e^{in\theta}.
\]

Ses coefficients conservent les puissances premières. On utilise l'involution géométrique \(\theta\mapsto-\theta\) et la conjugaison : \(\overline{\mathcal T_a(-\theta)}=\mathcal T_a(\theta)\). La projection de corrélation est

\[
\mathcal R_N=\frac{e^{aN}}{2\pi}\int_0^{2\pi}
 \mathcal T_a(\theta)\overline{\mathcal T_a(-\theta)}e^{-iN\theta}\,d\theta.
\tag{P}
\]

L'orthogonalité des caractères du cercle et la convergence absolue montrent sur papier que cette projection retient exactement le coefficient arithmétique additif de degré N. La justification élémentaire est \(0\le\Lambda(n)\le\log n\le n\) pour \(n\ge1\); elle paie la convergence uniforme et l'échange intégrale/séries. (P) est une projection de traces dans l'espace continu, sans crible, inversion de Möbius, décomposition de Vaughan ou estimation de progressions. Ce n'est pas une estimation de formes bilinéaires arithmétiques.

## Restes fermés de projection seulement

Poser \(r=e^{-a}\in(0,1)\),

\[
A(a)=\frac r{(1-r)^2},\qquad
B(a,M)=r^{M+1}\left(\frac{M+1}{1-r}+\frac r{(1-r)^2}\right).
\]

La troncature de la trace aux fréquences \(n\le M\) possède un reste uniforme au plus \(B\). La corrélation possède alors un reste de projection au plus \(2e^{aN}AB\), fermé et continu en \(a>0\) pour chaque entier M. Pour \(M\ge N\), la projection exacte de ce reste est même nulle, par les fréquences positives; ce fait ne supprime pas l'erreur d'évaluation ou de quadrature.

Une quadrature périodique exacte sur K nœuds, appliquée à la trace infinie, a uniquement les fréquences parasites \(N+\ell K\) si \(K>N\). Comme le coefficient de degré m est au plus \(m(m^2-1)/6\le m^3/6\), son erreur normalisée est majorée par

\[
E_{\rm alias}=\frac16\left[
N^3\frac q{1-q}+3N^2K\frac q{(1-q)^2}
+3NK^2\frac{q(1+q)}{(1-q)^3}
+K^3\frac{q(1+4q+q^2)}{(1-q)^4}\right],
\quad q=e^{-aK}.
\]

Cette enveloppe est fermée et continue pour \(a>0\). Les trois séries géométriques dérivées jusqu'à l'ordre 3 et l'orthogonalité discrète restent à prouver dans Lean. Si chaque trace nodale est réellement enfermée dans un disque de rayon \(\varepsilon\), la propagation supplémentaire est \(e^{aN}(2A+\varepsilon)\varepsilon\). Le rayon \(\varepsilon\) n'est pas un champ libre acceptable dans un banc : il faudrait le produire depuis les primitives, les restes spectraux et les arrondis vérifiés à chaque nœud. Aucun tel producteur uniforme en \(\theta\) n'existe dans le paquet C5 actuel.

## Verrous précis

L'objet H1 déjà étudié est seulement \(H_Y=-a\,\partial_a\mathcal T_a(0)\), pour \(a=1/Y\). Une identité à \(\theta=0\), même certifiée, ne fournit pas les phases nécessaires à (P). Il faut établir la vraie représentation Mellin/spectrale de \(\mathcal T_a(\theta)\), uniformément pour \(\operatorname{Re}(a-i\theta)>0\), avec branches, dérivées logarithmiques de la vraie zêta, convergence et restes fermés. Aucun résultat générique de trace ni fonction abstraite remplaçant zêta ne paie cette étape.

Il faut ensuite isoler la trace des premiers des résonances de puissances propres, conserver explicitement les projections correctrices, puis raccorder le coefficient obtenu à la définition canonique de \(D_N\), ses restrictions de frontière et ses unités. Rien ici ne suppose leur signe ni la cible \(D_N\le N/(256\log N\log\log N)\).

À \(N=10^8\), la condition conservatrice \(K>N\) représente plus de \(10^8\) nœuds distincts, sans coût mesuré disponible. Le banc thermique H1 courant (204800 nœuds verticaux, phase nulle) ne constitue pas ce banc de projection. Un choix \(a=1/N\) limiterait le facteur de normalisation à e, mais requiert un nouveau contrat spectral; le choix courant \(a=1/\sqrt N\) porte un facteur \(e^{\sqrt N}\) et ne permet pas de transférer gratuitement les rayons actuels. Aucune promesse de faisabilité temporelle ou de précision globale n'est faite.
