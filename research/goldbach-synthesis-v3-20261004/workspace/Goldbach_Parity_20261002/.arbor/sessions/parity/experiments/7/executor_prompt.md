## Codebase

Working directory: D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002

## Git Isolation

Work in the assigned experiment branch/worktree. Do not switch back to the main repository for implementation or evaluation.

## Research Idea

**ID**: 7
**Hypothesis**:
Mechanism: Determinant representation of the fixed additive HH level with actual signed factor weights.
Hypothesis: A Hecke or lattice decomposition may expose an arithmetic signed cancellation unavailable to a universal affine chart.
Observable: Exact bijection preserving all selectors and coefficients, numerical falsifier at N=100000000, and an independent quantitative cost audit before formalization.
Conflicts: Replacing actual Mobius weights by arbitrary coefficients restores the known operator barrier; fixed determinant geometry alone does not imply a saving.

## Evaluation Info

- **Evaluation command (B_dev)**: `& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002/round5/build-judge.ps1'`
- **Dataset info**: Source monographie 51p et continuation; sources Lean sprint15 préservées; tests entiers exploratoires N=100000000. Aucun B_test statistique.
- **Baseline score**: 0
- **Current trunk score**: 0

Use B_dev for final experiment scoring. Do NOT use B_test.

## Insights From Prior Experiments

- ROOT: Children findings: [1, done, score=0] Children findings: [1.1, done, score=0] Poids quadratique exact, Omega multiplicité, rugosité complète impose Omega≤3 et détecte un premier. La frontière r>alpha seule ne fournit ni ces hypothèses ni la primalité de m=kr. | [2, done, score=0] Aucun transport admissible avec défaut payé. La permutation conserve la somme ; les faces et variations de poids restent charges sans signe favorable. | [3, done, score=0] Le coefficient Möbius long est éliminé par inversion quartique exacte sur r<N≤alpha^4 ; le coefficient réel arbitraire conserve le tuple entier. La combinaison -6,+4,-1 reste à estimer. | [4, pruned, score=0] Le commutateur harmonique survit. Après le contre-exemple m303 à deux sites, le bloc complet 101,303,707,2121 avec n déplacé est strictement défavorable, même sans extrémité géométrique. Le contrôle global reste ouvert. | [5, done, score=0] Children findings: [5.1, done, score=0] J9/J10 prouvées sur ZMod q composite avec vraie somme des fréquences nonunitaires. Le défaut peut porter toute la masse quand tau=0 ; sommation jointe restaure une identité physique mais pas un gain signé. | [6, done, score=0] An independent cross-branch...

## Additional Context

Separate round5 Judge builder certifies this round after its numeric gates; wait until that builder and sources are final. No Git branch exists; source folders are isolated. No analytic target is assumed. Prior builders certify only their own prior modules.

## Instructions

1. Understand the code before editing.
2. Implement the idea faithfully.
3. Run quick checks to ensure the new logic is active.
4. Iterate on implementation bugs.
5. Run the B_dev evaluation when credible.
6. Report Changes, Baseline vs Result, Score, and Insight. The score must be the absolute primary metric, not a delta.

Save results to `results/7-<brief-description>/`.
