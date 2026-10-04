# Sous-contrat autonome Ψ/C5 — SOURCE ONLY

Destinataire proposé : ROLE3, dès qu'un slot est disponible et sous coordination
ROOT. Ce document autorise uniquement la lecture des sources et la rédaction
de preuves dans l'ownership ROLE3. Il ne constitue aucune gate Lean, aucun
producteur ou banc ; zéro nouveau calcul, probe/version ou installation.

## Objets réels et première cible substantielle

Mathlib4.15 cache = q356-canonical-binding-replay/.lake/packages/mathlib.
Définir psi(z)=deriv Complex.Gamma z / Complex.Gamma z, avec vraie Γ.
Sur Re(z)>0, construire (sans prémisse analytique supplémentaire) :

    psi(z+1)=psi(z)+1/z,
    psi(1)=-(Real.eulerMascheroniConstant:Complex),
    psi(z)=-gamma_E + ∫_(u>0)
                  [exp(-u)-exp(-zu)]/[1-exp(-u)] du.          P1

Les dérivées de Γ sont dans Gamma/Deriv ; Γ non nulle dans Gamma/Beta ;
la valeur en1 dans NumberTheory/Harmonic/GammaDeriv. Le cache recherché ne
fournit pas P1 directement. La récurrence et la valeur en1 sont accessibles
immédiatement à partir des vraies identités Γ et de leurs domaines.

Route proposée vers P1 : approximation GammaSeq/Beta sur Re(z)>0, convergence
holomorphe locale avec majorant concret, puis logarithme dérivé du produit fini.
Identifier la limite à
-gamma_E + Σ_(n≥0)[1/(n+1)-1/(n+z)]. La différence se garde entière.
Représenter chaque différence comme une intégrale Laplace, puis sommer
géométriquement avec un dominateur effectivement intégrable. Alternativement,
prouver cette série par une vraie limite sous l'intégrale Beta. Toute égalité
Γ′/Γ → série, tout échange limite/dérivée ou somme/intégrale doit être payé.
Pas de `hPsiIntegral`, `hWeil`, `hTrace`, majorant libre ou fonction générique
appelée psi dans la conclusion. Les seules prémisses finales sont Re(z)>0.

Au voisinage u=0, le numérateur de P1 s'annule : utiliser une formule exacte
e^-u-e^-zu = (z-1)u∫_(v=0..1)exp(-u(1+v(z-1)))dv pour construire O(u),
et 1-e^-u≥u/2 pour 0<u≤1. À l'infini, Re(z)>0 donne une exponentielle
intégrable après min(1,Re(z)) ; le dénominateur≥1-e^-1 est positif.
Ces bornes doivent être locales et uniformes lorsqu'une dérivation est utilisée.

## C5 fixé, aucun terme archimédien redéfini

ROLE1 source gelée : round22/role1_bridge/contour_formula22.md
SHA42faea33cdcd56c08f6fb593dbd42c5c293b8e72beb9c823db68e9576ac1edb7.
Lire FULL ce papier avant d'adapter les conventions. Poser Y≥1,
f_Y(x)=(x/Y)exp(-x/Y), G(s)=Y^sΓ(s+1), d=-1/2.
χ(s)=2(2π)^(s-1)sin(πs/2)Γ(1-s), vraie équation fonctionnelle.

    Iχ=(1/(2π)) ∫_(t∈R) G(d+it) χ′(d+it)/χ(d+it) dt.
    Arch_Y=∫_(x>1)
      [f_Y(x)+f_Y(1/x)/x-2f_Y(1)/x]/(x-1/x) dx.

La cible exacte est

    Iχ=(log(4π)+gamma_E)f_Y(1)+Arch_Y-1.                   C5

La réécriture symétrique vraie de χ′/χ sur d est
logπ+1/s-(1/2)psi((1-s)/2)-(1/2)psi(1+s/2).
Les deux arguments ont partie réelle3/4. La duplication/récurrence Γ doit
fournir cette égalité, elle n'est pas prise en prémisse.

Après u=2v et inversion Mellin payée séparément par ROLE4, garder un seul
intégrande près de v=0. La dernière intégrale devient

    ∫_(v>0) [e^-v f_Y(e^-v)+e^-2v f_Y(e^v)
                                      -2e^-2v f_Y(1)]/(1-e^-2v) dv.

Son écart avec Arch_Y est ∫_(x>1)f_Y(x)/x dx -2log2·f_Y(1).
Les intégrales complémentaires de f_Y/x valent1-exp(-1/Y) etexp(-1/Y),
d'où le vrai -1 de C5. Payer les substitutions, les orientations et Fubini ;
ne jamais distribuer une différence en deux intégrales divergentes.

## Interfaces existantes, portée et ownership

ROLE4/h1_contour/MellinThermal22 et MellinThermalInversion22 donnent en source
le vrai raccord Mellin. ZetaReflection22 fournit χ sous la forme cos équivalente
du cache et sa réflexion logarithmique avec non-annulation dérivée.
ROLE4/ArchimedeanEndpoint22 et ArchimedeanTail22 construisent en source la
valeur amovible f_Y(1)/2 et l'intégrabilité du vrai Arch. Ces sources ne sont
pas compilées et doivent être lues/auditées avant toute future importation.
Γ3 seule a reçu auteur PASS puis Juge indépendant PASS ; cela ne valide pas P1.

Écrire uniquement role3/h1_psi/** et un rapport SOURCE autonome, sans modifier
les captures, sources ou préparations antérieures. Pour chaque API, consigner
SHA, lecture FULL ou lignes TARGETED et capture honnête. Toute déclaration
nouvelle reçoit son #print axioms qualifié futur ; aucune exécution avant gate.
Un premier paquet récurrence + valeur en1 n'est pas une victoire ni P1/C5.
Le rapport identifie explicitement la première dette encore ouverte, sans
promouvoir un résultat générique avec P1 en hypothèse en vraie identité.
