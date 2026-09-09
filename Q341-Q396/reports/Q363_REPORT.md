# Q363 - Reduction de phase aux demi-entiers

## Verdict

```text
Q363_MOD4_TRIANGULAR_PARITY_PASS
Q363_EXPONENTIAL_PHASE_REDUCTION_PASS
Q363_COSINE_PHASE_REDUCTION_PASS
Q363_GENERIC_NUMERATOR_ZERO_PASS
Q363_HALF_INTEGER_ZERO_MATCH_PASS
Q363_DIRECT_BUILD_PASS
Q363_AXIOM_AUDIT_PASS

Q363 : CLOSED
```

Le developpement a ete gele a `2026-08-20T14:14:25.8743224+02:00`, apres
869 secondes et avant la freeze obligatoire de 16:44:56. Les sources n'ont
plus ete modifiees apres cet instant.

## Resultat terminal

Lean 4.15.0 prouve pour tout entier :

```lean
theorem publishedFNumerator_zero_at_halfInteger (n : Int) :
    Q362Probe.publishedFNumerator (Q362Probe.halfInteger n) = 0
```

Le zero commun avec le denominateur Q362 est aussi assemble :

```lean
theorem publishedF_common_zero_at_halfInteger (n : Int) :
    Q362Probe.publishedFNumerator (Q362Probe.halfInteger n) = 0 /\
      Q362Probe.publishedFDenominator (Q362Probe.halfInteger n) = 0
```

## Chaine formelle

`Mod4Triangular.lean` prouve l'exhaustivite des quatre residus entiers modulo
quatre et calcule exactement

```text
triangularInt n = n*(n+1)/2
```

modulo deux. Le signe est positif dans les classes 0 et 3, negatif dans les
classes 1 et 2.

`ExponentialPhase.lean` prouve d'abord l'identite algebrique

```text
(n+1/2)^2/2 + 3/8 = n*(n+1)/2 + 1/2
```

puis reduit l'exponentielle complexe au signe quadriperiodique commun.

`CosinePhase.lean` reconstruit tout entier sous la forme `4*q+r`, reduit les
arguments aux angles `pi/4`, `3*pi/4`, `5*pi/4`, `7*pi/4` par periodicite, et
obtient exactement le meme signe. La soustraction dans le numerateur publie
s'annule alors identiquement.

## Tentatives locales corrigees

Les premieres compilations ont detecte deux erreurs purement locales : un
facteur deux superflu dans la forme fermee de la classe 3, puis une ambiguite
de coercition entre la division entiere `n / 4` et la division complexe. Les
formes ont ete corrigees avant le gel. Aucun tableau externe, aucune valeur
numerique admise et aucun raccourci logique n'ont ete utilises.

## Audit

```text
Lean direct 4.15.0 : 6/6 modules PASS
Agregat Q363       : PASS
Axiomes terminaux  : propext, Classical.choice, Quot.sound
Scan interdit      : vide
Q362 preflight     : manifeste 21/21 PASS
HEAD/origin-main   : 433e29e / 433e29e
Git permanent      : aucune operation
```

Les avertissements restants sont uniquement des suggestions de linter
(`unnecessarySimpa` et `unusedTactic`) dans deux preuves deja compilees.

## Frontiere fail-closed

Q363 ne construit aucune singularite amovible et ne definit pas l'extension
entiere globale. Ces travaux appartiennent exclusivement a Q364.

```text
Q363                              : CLOSED
Q364_ENTIRE_EXTENSION             : READY / NOT_STARTED
RIEMANN_SIEGEL_DECOMPOSITION      : OPEN
ARIAS_REMAINDER                   : OPEN
BRIDGE_A                          : OPEN
CARRIER_MEMBERSHIP                : UNPROVED
TS340_UNCONDITIONAL               : OPEN_FROZEN
```

