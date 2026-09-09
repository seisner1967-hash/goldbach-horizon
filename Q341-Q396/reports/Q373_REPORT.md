# Q373 — Source F Harmonic Real Gap

## Verdict

```text
Q373_SOURCE_F_BORDER_EXTENSION_PASS
Q373_SOURCE_F_REAL_BOUNDARY_PASS
Q373_SOURCE_F_UPPER_HALF_PLANE_POSITIVITY_PASS
Q373_SOURCE_F_LOWER_HALF_PLANE_POSITIVITY_PASS
Q373_SOURCE_F_UNIFORM_TAIL_PASS
Q373_SOURCE_F_REAL_GAP_UNIFORM_PASS
Q373_SOURCE_F_REAL_GAP_SPECIALIZATION_PASS
Q370_PRODUCT_BOUND_UNCONDITIONAL_PASS
Q370_FUBINI_UNCONDITIONAL_PASS
Q373_DIRECT_BUILD_PASS
Q373_AXIOM_AUDIT_PASS
```

Classification: `PROVEN_IN_LEAN`.

## Resultats terminaux

La fonction utilisee est exclusivement la fonction logarithmique source de 2024:

```lean
sourceH z := 1 + Q366Probe.sourceF z
sourceG z := Complex.exp (-sourceH z)
```

Lean prouve notamment:

```lean
sourceH_re_pos_of_im_pos : 0 < z.im -> 0 < (sourceH z).re
sourceH_re_pos_of_im_neg : z.im < 0 -> 0 < (sourceH z).re
sourceF_real_gap_uniform :
  a <= 1 + (sourceF (sourceLinePoint (1/2) phi y)).re
```

La constante `a` est strictement positive et uniforme en `phi` dans le wedge
`theta/2 <= phi <= pi-theta/2` et en `y : Real`. Elle est extraite par compacite
sur `|y| <= 17`, puis combinee avec la queue explicite
`(sourceH z).re >= 1/4`.

L'extension de bord est egalement fermee:

```lean
sourceGBoundary 0 = exp (-1)
sourceGBoundary 1 = 0
tendsto_sourceGBoundary_nhdsNE_zero
sourceGBoundary_continuousAt_one
```

Au voisinage de `1`, la preuve quantitative utilise:

```text
norm (sourceG z) <= exp (5/2) * norm (1-z)^(3/4).
```

## Raccord Q370

Le temoin conditionnel `SourceFRealGap` est maintenant habite par
`q370SourceFRealGap`. Avec la minoration cosinus compilee apres la deadline de
RS3H-II, Lean prouve sans premisse de gap residuelle:

```lean
norm_sourceDoubleKernel_le_rsProductMajorant_unconditional
sourceRSRemainder_fubini_unconditional
```

## Confiance

- 17 sources Q373, 1500 lignes.
- Compilation directe de chaque source: PASS.
- Agregat Lake: PASS.
- Axiomes terminaux: `propext`, `Classical.choice`, `Quot.sound`.
- Scan executable interdit: vide.

La fonction `sourceF` n'est jamais confondue avec
`Q364Probe.riemannSiegelF`.
