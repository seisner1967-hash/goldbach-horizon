# Q362 - Fonction auxiliaire entiere de Riemann-Siegel

## Verdict

```text
Q362_PRIMARY_F_DEFINITION_PASS
Q362_PRIMARY_CANDIDATE_CORRECTED
Q362_DENOMINATOR_ZERO_SET_PASS
Q362_DENOMINATOR_SIMPLE_ZERO_PASS
Q362_NUMERATOR_ZERO_AT_N0_PROTOTYPE_PASS
Q362_HALF_INTEGER_ZERO_MATCH_PARTIAL

Q362_GENERIC_REMOVABLE_SINGULARITY_PASS : NOT_OBTAINED
Q362_AUXILIARY_F_ENTIRE_PASS             : NOT_OBTAINED
Q362_QUOTIENT_AGREEMENT_PASS             : NOT_OBTAINED
Q362_DERIVATIVE_INTERFACE_PASS           : NOT_OBTAINED

Q362 : ANALYTIC_PARTIAL_FAIL_CLOSED
```

Le developpement a ete gele a `2026-08-20T13:47:25.8338393+02:00`, avant la
freeze obligatoire de 14:05 et l'echeance de 14:20.

## Source primaire

La definition a ete transcrite depuis Juan Arias de Reyna, *High precision
computation of Riemann's zeta function by the Riemann-Siegel formula, I*,
Math. Comp. 80 (2011), page 996, equations (2.4)-(2.5), DOI
`10.1090/S0025-5718-2010-02426-3`.

La formule publiee est

```text
       exp(pi*i*(z^2/2 + 3/8)) - i*sqrt(2)*cos(pi*z/2)
F(z) = -------------------------------------------------
                         2*cos(pi*z)
```

et l'article affirme que cette fonction est entiere. Le candidat preliminaire
`cos(pi*(z^2/2+3/8))/cos(pi*z)` est donc rejete.

La capture de la page primaire est archivee dans
`Q362Research/AriasDeReyna2011_p996_eq2.4-2.5.png`. Les trois pseudo-PDF
renvoyes par la protection web AMS etaient des pages HTML de challenge; ils
ont ete supprimes et ne figurent pas dans le paquet.

## Resultats Lean compiles

`Q362Probe.PrimaryDefinition` definit exactement le numerateur, le
denominateur et le quotient publies, puis prouve :

- la differentiabilite complexe du numerateur et du denominateur;
- `publishedFDenominator z = 0` si et seulement si
  `z = n + 1/2` pour un entier `n`;
- la non-nullite de la derivee du denominateur en chaque demi-entier.

`Q362Probe.HalfIntegerZeros` prouve en outre le zero commun du numerateur au
point temoin `z = 1/2` (`n = 0`). Ce cas compile sans oracle numerique.

## Frontiere fail-closed

La preuve generique du zero du numerateur pour tout `n : Int` n'a pas ete
terminee. Elle requiert encore la reduction periodique modulo 4 de la phase
exponentielle et du cosinus. La porte B du mandat n'etant donc pas franchie,
aucune construction de singularite amovible, aucun recollement global et
aucun objet entier `F` n'ont ete tentes.

La definition `riemannSiegelFDeriv` enregistre seulement la signature attendue
par l'equation (2.4); elle ne constitue pas l'interface de derivees de la
fonction entiere, puisque cette derniere n'a pas ete construite.

## Audit

```text
Lean direct 4.15.0 : 3/3 modules PASS
Lake               : bloque par SSL avant compilation
Axiomes            : propext, Classical.choice, Quot.sound
Scan interdit      : vide
HEAD/origin-main   : 433e29e / 433e29e
Git permanent      : aucune operation
```

L'echec `lake` est environnemental; les trois sources ont ete compilees avec
le binaire Lean 4.15.0 epingle et les caches Mathlib locaux.

## Frontiere globale

```text
Q361_RIEMANN_SIEGEL_DECOMPOSITION : OPEN
Q361_ARIAS_REMAINDER              : OPEN
BRIDGE_A                           : OPEN
CARRIER_MEMBERSHIP                 : UNPROVED
TS340_UNCONDITIONAL                : OPEN_FROZEN
Q363                               : NOT_STARTED
```

