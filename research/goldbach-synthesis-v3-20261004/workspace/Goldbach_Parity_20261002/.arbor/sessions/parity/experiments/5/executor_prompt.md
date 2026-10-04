## Codebase

Working directory: D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round3

## Git Isolation

Work in the assigned experiment branch/worktree. Do not switch back to the main repository for implementation or evaluation.

## Research Idea

**ID**: 5
**Hypothesis**:
Mechanism: Regroupement des coefficients HH réels par quotient modulo N puis projection multiplicative.
Hypothesis: La direction signée H(a)mu(s)mu(t) peut admettre un contrôle plus fin que la norme du noyau à coefficients arbitraires.
Observable: Histogramme rationnel exact N=100000000, identité de transformée validée, puis estimation indépendante avec masques et non-unités conservés.
Conflicts: Les masques joints empêchent une factorisation naïve et les grands conducteurs ne sont pas couverts par le seul input de petits modules.

## Evaluation Info

- **Evaluation command (B_dev)**: `& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round3\build-judge.ps1'`
- **Dataset info**: Source monographie 51p et continuation; sources Lean sprint15 préservées; tests entiers exploratoires N=100000000. Aucun B_test statistique.
- **Baseline score**: 0
- **Current trunk score**: 0

Use B_dev for final experiment scoring. Do NOT use B_test.

## Insights From Prior Experiments

- ROOT: Children findings: [1, done, score=0] Children findings: [1.1, done, score=0] Poids quadratique exact, Omega multiplicité, rugosité complète impose Omega≤3 et détecte un premier. La frontière r>alpha seule ne fournit ni ces hypothèses ni la primalité de m=kr. | [2, done, score=0] Aucun transport admissible avec défaut payé. La permutation conserve la somme ; les faces et variations de poids restent charges sans signe favorable. | [3, done, score=0] Le coefficient Möbius long est éliminé par inversion quartique exacte sur r<N≤alpha^4 ; le coefficient réel arbitraire conserve le tuple entier. La combinaison -6,+4,-1 reste à estimer. | [4, pruned, score=0] Le facteur harmonique laisse un commutateur non nul ; m303 donne D-W=log101/2 et une contribution Sfull négative. La fermeture favorable point par point est fausse. [Pruned: Hypothèse de signe favorable point par point réfutée par noyau littéral m303 ; ne pas inférer un no-go global.]

## Additional Context

Source agent2_projection.md P1-P10. Lean ZMod N composite avec unités et AddChar/MulChar. Filtre multifibre.json PASS avant certification. Audit grand conducteur, masques et non-unités ; aucune supposition de cible. Juge frais round3/judge séparé, anciens reçus préservés. Attribution de victoire strictement sémantique.

## Instructions

1. Understand the code before editing.
2. Implement the idea faithfully.
3. Run quick checks to ensure the new logic is active.
4. Iterate on implementation bugs.
5. Run the B_dev evaluation when credible.
6. Report Changes, Baseline vs Result, Score, and Insight. The score must be the absolute primary metric, not a delta.

Save results to `results/5-<brief-description>/`.
