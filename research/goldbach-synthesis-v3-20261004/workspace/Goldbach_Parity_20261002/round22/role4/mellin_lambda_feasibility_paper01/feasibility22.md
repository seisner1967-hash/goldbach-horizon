# Faisabilité Mellin–Λ sur le cercle, N=10^8 — PAPER seulement

Cette note distincte conserve tous les fichiers gelés. Elle ne rapporte aucun calcul, test, import candidat, probe ou compilation. Le cercle en vraie Λ est acquis dans Envelope11/Identity13. L'échange infini Lambda30 et EΛ16 restent SOURCE non validés par leur compilateur. Pendant sa rédaction, le vrai lot30 a fermé Tail03 avec exit0 et 22 impressions standards : son reçu, son log et l'observation ROOT à01:07:15.363523UTC ont été lus FULL ; l'état officiel est86 modules/1456 déclarations, définitions incluses. Ce PASS porte sur la queue Gamma non pondérée ; il ne valide pas EΛ. Aucun verdict futur n'est anticipé. Les déductions nouvelles ci-dessous sont PAPER. Elles ne produisent ni minoration, ni annulation canonique, ni borne de D_N.

## 1. Coefficient et enveloppe à construire

Pour a>0, N entier naturel, toutes les puissances premières sont conservées :

\[
P(w)=\sum_{n\ge0}\Lambda(n)e^{-nw},\quad
D(t)=\sum_{n\ge0}\Lambda(n)n^{-2-it},\quad
K(w,t)=\Gamma(2+it)w^{-2-it}.
\]

La puissance complexe est principale. Le cercle acquis identifie le coefficient
\(C_N=\sum_{n=0}^N\Lambda(n)\Lambda(N-n)\). Sa version centrée s'écrit

\[
C_N=\frac{e^{aN}}{2\pi}\int_{-\pi}^{\pi}P(a-i\theta)^2e^{-iN\theta}\,d\theta.
\tag{C}
\]

Les coefficients réels expliquent le carré : la corrélation initiale est
\(P(a-i\theta)\overline{P(a+i\theta)}\). Le petit raccord de translation de l'intervalle acquis [0,2π] vers [-π,π] repose sur la périodicité de la vraie série absolument convergente et du caractère entier. Il reste à écrire comme bridge si la future formalisation exige cet intervalle. **Aucune périodicité de P_H ou de la puissance principale n'en découle.**

Pour H≥0, définir directement sur cet intervalle centré

\[
P_H(w)=\frac1{2\pi}\int_{-H}^H D(t)K(w,t)dt,\qquad
C_{N,H}(a)=\frac{e^{aN}}{2\pi}\int_{-\pi}^{\pi}P_H(a-i\theta)^2e^{-iN\theta}d\theta.
\]

Le contrat EΛ SOURCE propose
\(|P(w)-P_H(w)|\le 6C(w)e^{-\delta(w)H}/(\pi\delta(w))\), où
\(\eta=(\pi/2+|\operatorname{Arg}w|)/2\),
\(\delta=(\pi/2-|\operatorname{Arg}w|)/2>0\),
\(C=|w|^{-2}\sec^2\eta\). Il faut intégrer les deux queues pondérées D·K ; une erreur de Gamma seule ne remplace pas ce contrat.

## 2. Géométrie PAPER : un majorant plus serré

Poser u=|θ| et r=√(a²+u²). Les lemmes manquants de géométrie sont :

1. a−iθ est dans le demi-plan droit/slitPlane et Arg(a−iθ)=−atan(θ/a), avec la branche principale effectivement identifiée.
2. Pour u>0, π/2−atan(u/a)=atan(a/u), les deux angles appartenant à (0,π/2) ; pour u=0, δ=π/4.
3. cos(atan(u/a))=a/r, sin(atan(u/a))=u/r et l'identité de demi-angle avec les signes positifs.
4. Monotonie et continuité des fonctions résultantes, puis transport de ces bornes à l'intégrale réelle compacte. Ces conclusions ne sont pas annoncées comme Lean PASS.

Ces identités donnent sur papier, **en conservant la relation entre norme et argument**,

\[
C(a-i\theta)=\frac{2}{a^2}\left(1+\frac{u}{r}\right),\qquad
\delta(a-i\theta)\ge d(a):=\frac12\arctan(a/\pi)>0.
\]

C est croissant en u ; δ est décroissant. Pour H≥0, e^(−δH)/δ est décroissant en δ. Le maximum du rayon sur |θ|≤π est donc atteint à u=π, et vaut

\[
\bar C(a)=\frac{2}{a^2}\left(1+\frac{\pi}{\sqrt{a^2+\pi^2}}\right)<\frac4{a^2},\quad
\epsilon(a,H)=\frac{6\bar C(a)}{\pi d(a)}e^{-d(a)H}.
\tag{U}
\]

Ce majorant améliore le précédent compact C*=a^(−2)sec²((π/2+atan(π/a))/2) : séparer |w|≥a et l'angle maximal perdait leur relation et donnait un ordre a^(−4). La nouvelle borne est d'ordre a^(−2). Il s'agit d'un **nouveau raccord PAPER**, sans modification de l'ancien contrat gelé.

L'amplitude acquise du vrai P est
\(U(a)=e^{-a}/(1-e^{-a})^2\). Par |P_H|≤U+ε et la différence de deux carrés,

\[
|C_N-C_{N,H}(a)|\le
\mathcal E_N(a,H):=e^{aN}\bigl(2U(a)\epsilon(a,H)+\epsilon(a,H)^2\bigr).
\tag{ECOEF}
\]

Le terme ε² est nécessaire : l'intégrale tronquée P_H n'a pas le majorant |P_H|≤U du polynôme arithmétique partiel. Une enveloppe plus fine serait e^(aN)/(2π) fois l'intégrale de 2U EΛ+EΛ² sur le cercle ; (ECOEF) en est le majorant uniforme fermé. Pour N fixé, \(\mathcal E_N\) est continue conjointement sur a>0,H≥0, sous les identités géométriques ci-dessus. Aucun rayon de précision libre n'apparaît.

## 3. Hauteur requise : des inégalités, aucun banc

Pour une tolérance τ>0, le seuil exact de **cette enveloppe**, et non de l'erreur réelle inconnue, est

\[
\epsilon_*=
\frac{\tau e^{-aN}}{\sqrt{U(a)^2+\tau e^{-aN}}+U(a)},\qquad
H_*:=\max\left(0,\frac1{d(a)}\log\frac{6\bar C(a)}{\pi d(a)\epsilon_*}\right).
\tag{H}
\]

La forme rationnelle de ε* évite la soustraction de deux quantités presque égales. ECOEF≤τ équivaut à H≥H*. Tous les dénominateurs sont strictement positifs. Près de a=0, d(a)~a/(2π), C̄~4/a² et U~a^(−2), d'où
\(H_*\sim(2\pi/a)\log(96e^{aN}/(\tau a^5))\) dans ce régime ; cet équivalent ne remplace pas les gardes fermées.

Fixer maintenant N=10^8, a=1/N, τ=10^(−6). Les bornes élémentaires 3<π<7/2, 8/3<e<3, e^(−a)≥1−a et 2sinh(a/2)≥a donnent

\[
\tfrac12N^2<U(a)\le N^2,\quad
\frac1{8N}<d(a)<\frac1{6N},\quad
24N^3<\frac{6\bar C(a)}{\pi d(a)}<64N^3.
\]

La borne inférieure utilise C̄>2N² et d≤1/(2πN). La borne supérieure utilise C̄<4N² et π+a<4, avec atan(x)≥x/(1+x), x≥0. Cette dernière inégalité suit de la différence de dérivées 2x/((1+x²)(1+x)²)≥0 et de l'égalité en zéro.

**Suffisance : H=10^11.** Alors dH>125 et e^125>10^50, car e>8/3 et (8/3)^5>100. Ainsi ε<64·10^(−26), et
\[
\mathcal E_N\le9N^2\epsilon<576\cdot10^{-10}<10^{-6}.
\]
Le passage à 9N²ε utilise ε≤N² et e<3. Ce choix laisse donc une marge positive pour d'autres erreurs, mais ne paie pas celles-ci.

**Insuffisance de l'enveloppe : H≤5·10^10.** Dans ce cas dH<90 et e^90<3^90<10^45, puisque 3^10=59049<10^5. La partie linéaire de ECOEF suffit à donner
\[
\mathcal E_N>48N^5e^{-dH}>48\cdot10^{-5}>10^{-6}.
\]
Donc \(5\cdot10^{10}<H_*<10^{11}\). Ces bornes n'affirment **aucun minorant sur l'erreur réelle** : elles quantifient seulement ce que le majorant proposé peut certifier. La longueur de l'intégrale intérieure est 2H ; elle dépasse déjà 10^11 pour le seuil de cette enveloppe.

## 4. Autres erreurs à fermer et coût fini

**Troncature de D.** Si D_M est la somme n≤M, M≥2, Λ(n)≤log n et le test intégral décroissant de log(x)/x² donnent
\[
|D-D_M|\le b_M:=\frac{\log M+1}{M},\quad
|P_H-P_{H,M}|\le
\frac{b_M\bar C(a)}{\pi d(a)}(1-e^{-d(a)H}).
\tag{ED}
\]
Ce sont des queues de série absolument convergente, sans reste de progression. Dans le cas fixé, le dernier facteur est <(32/3)N³ b_M. À titre de **choix suffisant théorique**, M=10^52 donne log M<156, donc une erreur de trace <(5024/3)·10^(−28). Cette somme littérale exige 10^52 termes par valeur de D, avant même les primitives et la quadrature. Ce choix n'est ni nécessaire pour l'erreur réelle, ni un catalogue disponible. L'autre majorant 4/√M du test n^(−3/2) est encore moins favorable. Utiliser plutôt −ζ′/ζ exige une identification et un évaluateur certifié uniformes effectivement reliés à D ; main30 ne les fournit pas.

**Quadrature extérieure.** Un exemple de garde fermée, volontairement grossier, peut être dérivé sans périodicité de P_H. La vraie dérivée en θ du noyau est i(2+it)K/w. Poser
\[
m_0=(1-e^{-dH})/d,\quad m_1=(1-e^{-dH}(1+dH))/d^2,\quad
V_H=\frac{6\bar C}{\pi a}(2m_0+m_1),\quad A_H=U+\epsilon,
\]
\[
L_H=2A_HV_H+N A_H^2.
\]
Alors |∂θP_H|≤V_H et |∂θ(P_H²e^(−iNθ))|≤L_H. Le transfert de dérivée sous l'intégrale finie reste un lemme à payer, avec la domination concrète (2+|t|)|K|/a. Pour J cellules égales et leurs milieux exacts, la garde de projection est
\[
E_{\rm circle}\le e^{aN}\pi L_H/(2J).
\tag{EQ}
\]
Elle suit de l'intégrale de la distance au milieu dans chaque cellule, et est continue dans a>0,H≥0 pour J fixé. À N=10^8,H=10^11, les mêmes inégalités donnent V_H≤128N^4+512N^5, A_H≤2N², L_H≤2564N^7. Ainsi J=10^67 serait un choix suffisant pour EQ<15384·10^(−11)<τ/4. Ce nombre exprime l'inefficacité de cette garde Lipschitz ; il ne démontre pas que toute quadrature requiert J aussi grand. Des méthodes d'ordre élevé demandent leurs propres restes dérivés. On ne peut importer l'aliasing exact du polynôme fini ni une convergence périodique exponentielle pour P_H sans payer ses deux bords.

**Quadrature intérieure en t.** ED ne paie pas le remplacement de l'intégrale par des cellules. Il faut un producteur de Γ, du cpow et de D, des domaines complexes explicites jusqu'à |t|=H, et des majorants de dérivées/Cauchy ou de variation du produit concret D·K. Les restes doivent être intégrés cellule par cellule. La domination L1 seule n'est pas un reste de quadrature. Aucun tel évaluateur à H de cette taille et avec ces gardes n'est disponible dans ce paquet.

**Primitives, positions, poids, arrondi.** À des nœuds exacts, une erreur de trace effectivement certifiée s et une erreur de caractère χ donnent une erreur de produit ≤2A_H s+s²+(A_H+s)²χ. Le facteur e^(aN) transporte cette garde à la moyenne normalisée. Un décalage de nœud ρ coûte au plus e^(aN)L_Hρ, si le segment entre nœud exact et nœud évalué reste dans [-π,π] ; cette inclusion doit être contrôlée. La somme des erreurs absolues de poids coûte e^(aN)(A_H+s)²(1+χ) fois cette somme. Il faut encore certifier le normaliseur, l'accumulation dirigée et les erreurs de chaque primitive. s,χ,ρ ne sont pas des précisions libres du contrat : un futur checker doit les recalculer depuis les enclosures et les restes de son programme, puis échouer si le budget total dépasse τ. Aucun programme qui réalise ces gardes n'est remis ici.

## 5. Verdict de faisabilité et périmètre

Le contrat mathématique est fini, avec une enveloppe continue explicite. La géométrie améliorée élimine une perte artificielle de a^(−2), mais δ reste d'ordre 1/N. Le choix a=1/N force donc, pour ce majorant, H entre 5·10^10 et 10^11. Les choix littéraux de D et de la quadrature Lipschitz exhibent des coûts finis astronomiques ; ils ne constituent pas un évaluateur praticable sur ce PC. Aucun temps ni mémoire mesuré n'est annoncé, et cette note ne prouve pas l'impossibilité d'une meilleure méthode certifiée.

L'évaluateur global Mellin–Λ correspondant est **OPEN / NOT_PREPARED**. Les noyaux NTT natifs d'une autre route ne réalisent pas ces intégrales ; les clôtures numériques antérieures sans coefficient ne remplissent pas les gardes nouvelles. Les prochains petits lemmes utiles sont la géométrie exacte de C et δ, le transfert centré du vrai cercle, puis un reste de quadrature intérieure réellement construit. L'échange Λ et les queues pondérées doivent d'abord recevoir leurs véritables verdicts indépendants. Même une future évaluation de C_N n'impose ni signe aux traces spectrales, ni corrections PP/front, ni cible D_N. WIN reste ouvert.

Sources readonly : [contrat EΛ16](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_lambda_tail_source01/source_contract22.md), [handoff EΛ16](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/complex_gamma_mellin_lambda_tail_source01/source_handoff22.json), [Identity13](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/judge5/batch13/sources/ThermalProjectionIdentity22.lean), [Envelope11 exact](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/projection_envelope_revision02/ThermalProjectionEnvelope22.lean). Les hash et scopes de lecture figurent dans read_receipts22.json ; cette note n'autorise aucune exécution.

Statut Tail lu : [reçu30](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/judge5/batch30/batch30_attempt01/receipt.json), [log30](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/judge5/batch30/batch30_attempt01/ComplexGammaMellinTail22.log), [observation ROOT30](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/.arbor/sessions/parity/.coordinator/messages/round22_judge_batch30_closed_observation.json), une compilation indépendante close, aucune exécution par l'auteur de cette note.
