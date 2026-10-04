## Codebase

Working directory: D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002

## Git Isolation

Work in the assigned experiment branch/worktree. Do not switch back to the main repository for implementation or evaluation.

## Research Idea

**ID**: 1
**Hypothesis**:
Mechanism: Projecteurs Möbius de parité et correction des fibres triprimes.
Hypothesis: Isoler exactement les contributions impaires excédant les premiers révèle la masse à compenser sans changer le support.
Observable: Identité arithmétique Lean compilée et filtre exact N=100000000 ; victoire seulement avec contrôle additif effectif de la correction.
Conflicts: La parité seule laisse les triprimes ; la correction doit être explicite et ne peut être supposée petite.

## Evaluation Info

- **Evaluation command (B_dev)**: `cd D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002; Lean compiler plus axiom audit 1`
- **Dataset info**: Source monographie 51p et continuation; sources Lean sprint15 préservées; tests entiers exploratoires N=100000000. Aucun B_test statistique.
- **Baseline score**: 0
- **Current trunk score**: 0

Use B_dev for final experiment scoring. Do NOT use B_test.

## Instructions

1. Understand the code before editing.
2. Implement the idea faithfully.
3. Run quick checks to ensure the new logic is active.
4. Iterate on implementation bugs.
5. Run the B_dev evaluation when credible.
6. Report Changes, Baseline vs Result, Score, and Insight. The score must be the absolute primary metric, not a delta.

Save results to `results/1-<brief-description>/`.
