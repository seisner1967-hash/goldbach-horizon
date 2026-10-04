## Codebase

Working directory: D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002

## Git Isolation

Work in the assigned experiment branch/worktree. Do not switch back to the main repository for implementation or evaluation.

## Research Idea

**ID**: 6
**Hypothesis**:
Mechanism: Uniformité de Möbius sur des formes affines conservant le niveau HH fixé.
Hypothesis: Un chart affine exact peut conserver les quatre signes et donner les gradients indépendants nécessaires aux théorèmes de complexité finie.
Observable: Audit primaire, test rationnel des intersections et certificat Lean du déterminant croisé nul ; nouveaux transferts nécessaires si le chart échoue.
Conflicts: Positivité/non-dégénérescence obligatoire, niveau multiplicatif et coefficients croissants ; presque tous les intervalles ne couvre pas chaque N.

## Evaluation Info

- **Evaluation command (B_dev)**: `& 'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002/round4/build-judge.ps1'`
- **Dataset info**: Source monographie 51p et continuation; sources Lean sprint15 préservées; tests entiers exploratoires N=100000000. Aucun B_test statistique.
- **Baseline score**: 0
- **Current trunk score**: 0

Use B_dev for final experiment scoring. Do NOT use B_test.

## Insights From Prior Experiments

- ROOT: Children findings: [1, done, score=0] Children findings: [1.1, done, score=0] Poids quadratique exact, Omega multiplicité, rugosité complète impose Omega≤3 et détecte un premier. La frontière r>alpha seule ne fournit ni ces hypothèses ni la primalité de m=kr. | [2, done, score=0] Aucun transport admissible avec défaut payé. La permutation conserve la somme ; les faces et variations de poids restent charges sans signe favorable. | [3, done, score=0] Le coefficient Möbius long est éliminé par inversion quartique exacte sur r<N≤alpha^4 ; le coefficient réel arbitraire conserve le tuple entier. La combinaison -6,+4,-1 reste à estimer. | [4, pruned, score=0] Le commutateur harmonique survit. Après le contre-exemple m303 à deux sites, le bloc complet 101,303,707,2121 avec n déplacé est strictement défavorable, même sans extrémité géométrique. Le contrôle global reste ouvert. | [5, done, score=0] Transformée exacte Kloosterman vers carré de Gauss prouvée pour ZMod N composite sur unités, avec conjugaison et poids réels extérieurs. Les grands conducteurs, les masques couplés et les phases non unitaires restent sans estimation suffisante.

## Additional Context

Source round4/agent1_uniformity.md. Certifier seulement le déterminant croisé avec hypothèse pour tous X,Y et N non nul ; pas un théorème global de rang sans non-dégénérescence. Filtre affine.json PASS avant compilation. Module AffineHHObstruction sans import ancien Goldbach, logs et Juge frais round4, score victoire sémantique.

## Instructions

1. Understand the code before editing.
2. Implement the idea faithfully.
3. Run quick checks to ensure the new logic is active.
4. Iterate on implementation bugs.
5. Run the B_dev evaluation when credible.
6. Report Changes, Baseline vs Result, Score, and Insight. The score must be the absolute primary metric, not a delta.

Save results to `results/6-<brief-description>/`.
