## Codebase

Working directory: D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002

## Git Isolation

Work in the assigned experiment branch/worktree. Do not switch back to the main repository for implementation or evaluation.

## Research Idea

**ID**: 3
**Hypothesis**:
Mechanism: Inversion finie de convolution éliminant le Möbius long sur toute la frontière quart.
Hypothesis: Un reste supporté à partir de (alpha+1)^4 permet une expansion exacte à facteurs courts pour r<N sans imposer la rugosité de m.
Observable: Identité quartique et support du reste compilés après filtre exact N=100000000 ; contrôle ultérieur de combinaison additive nécessaire.
Conflicts: La piste 1 impose m rugueux, la piste 2 ne contrôle pas les bords ; ici le support complet est conservé mais aucune annulation analytique n'est présumée.

## Evaluation Info

- **Evaluation command (B_dev)**: `cd D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002; Lean compiler plus axiom audit 3`
- **Dataset info**: Source monographie 51p et continuation; sources Lean sprint15 préservées; tests entiers exploratoires N=100000000. Aucun B_test statistique.
- **Baseline score**: 0
- **Current trunk score**: 0

Use B_dev for final experiment scoring. Do NOT use B_test.

## Insights From Prior Experiments

- ROOT: Children findings: [1, done, score=0] Projecteurs exacts compilés sans axiome arithmétique ; triprime admissible conserve Podd=1 et Lambda=0. Correction triprime indispensable, gain additif absent. | [2, done, score=0] Aucun transport admissible avec défaut payé. La permutation conserve la somme ; les faces et variations de poids restent charges sans signe favorable.

## Instructions

1. Understand the code before editing.
2. Implement the idea faithfully.
3. Run quick checks to ensure the new logic is active.
4. Iterate on implementation bugs.
5. Run the B_dev evaluation when credible.
6. Report Changes, Baseline vs Result, Score, and Insight. The score must be the absolute primary metric, not a delta.

Save results to `results/3-<brief-description>/`.
