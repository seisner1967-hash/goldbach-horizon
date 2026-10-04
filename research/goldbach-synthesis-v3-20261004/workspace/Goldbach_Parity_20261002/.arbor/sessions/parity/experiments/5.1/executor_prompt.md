## Codebase

Working directory: D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002

## Git Isolation

Work in the assigned experiment branch/worktree. Do not switch back to the main repository for implementation or evaluation.

## Research Idea

**ID**: 5.1
**Hypothesis**:
Mechanism: Projection jointe des fréquences duales et des moments multiplicatifs de HH.
Hypothesis: Sommer h et l avant une norme peut restaurer l'échelle N sans perdre les vrais coefficients signés.
Observable: Identité de décomplétion avec reste nonunitaire exact, filtre rationnel/cyclotomique, audit des énergies et du gain logarithmique restant.
Conflicts: La dépendance h en s*t et les phases de caractères induits interdisent les annulations naïves ; revenir à l'échelle N ne prouve pas un gain.

## Evaluation Info

- **Evaluation command (B_dev)**: `& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002/round4/build-judge.ps1'`
- **Dataset info**: Source monographie 51p et continuation; sources Lean sprint15 préservées; tests entiers exploratoires N=100000000. Aucun B_test statistique.
- **Baseline score**: 0
- **Current trunk score**: 0

Use B_dev for final experiment scoring. Do NOT use B_test.

## Insights From Prior Experiments

- ROOT: Children findings: [1, done, score=0] Children findings: [1.1, done, score=0] Poids quadratique exact, Omega multiplicité, rugosité complète impose Omega≤3 et détecte un premier. La frontière r>alpha seule ne fournit ni ces hypothèses ni la primalité de m=kr. | [2, done, score=0] Aucun transport admissible avec défaut payé. La permutation conserve la somme ; les faces et variations de poids restent charges sans signe favorable. | [3, done, score=0] Le coefficient Möbius long est éliminé par inversion quartique exacte sur r<N≤alpha^4 ; le coefficient réel arbitraire conserve le tuple entier. La combinaison -6,+4,-1 reste à estimer. | [4, pruned, score=0] Le commutateur harmonique survit. Après le contre-exemple m303 à deux sites, le bloc complet 101,303,707,2121 avec n déplacé est strictement défavorable, même sans extrémité géométrique. Le contrôle global reste ouvert. | [5, done, score=0] Transformée exacte Kloosterman vers carré de Gauss prouvée pour ZMod N composite sur unités, avec conjugaison et poids réels extérieurs. Les grands conducteurs, les masques couplés et les phases non unitaires restent sans estimation suffisante.
- 5: Transformée exacte Kloosterman vers carré de Gauss prouvée pour ZMod N composite sur unités, avec conjugaison et poids réels extérieurs. Les grands conducteurs, les masques couplés et les phases non unitaires restent sans estimation suffisante.

## Additional Context

Source round4/agent2_joint_frequency.md J9/J10. Module CompositeCompletion, ZMod q non nul, Fourier standard, Gauss sur unités et vraie somme nonunitaire. Filtre inverse-completion requis avant certification. Ne pas supposer caractère primitif, tau non nul, ni disparition h0. Aucun gain analytique à déclarer sur simple inversion de complétion.

## Instructions

1. Understand the code before editing.
2. Implement the idea faithfully.
3. Run quick checks to ensure the new logic is active.
4. Iterate on implementation bugs.
5. Run the B_dev evaluation when credible.
6. Report Changes, Baseline vs Result, Score, and Insight. The score must be the absolute primary metric, not a delta.

Save results to `results/5.1-<brief-description>/`.
