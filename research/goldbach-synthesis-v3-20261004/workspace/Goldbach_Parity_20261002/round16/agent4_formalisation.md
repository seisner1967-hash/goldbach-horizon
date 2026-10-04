# Boucle16 — formalisation indépendante de la marge harmonique

**FINAL rôle4 : compilation nouvelle réussie, résultat auxiliaire, score0, victoryfalse.** Le module `round16/role4/LeastMissingPrimeMargin.lean` prouve sans hypothèse sur S(N) le volet harmonique de A7. Il est transmis au rôle3 pour le raccord au produit singulier réel et aux facteurs locaux forcés. Il ne démontre ni disponibilité d’une paire q,N−p0q, ni comparaison globale des capacités, ni la cible D_N.

Le rôle4 a lu PROBE_BLOCK16, le retour définitif15, le FINAL conceptuel2 et la source réelle `round11/lean/ThreeAdicPrimePairing.lean`. Les701 archives restent intactes. Le skill executor Arbor est appliqué dans le périmètre isolé affecté par le coordinateur, sans Git ni modification des autres rôles. Aucun ancien module, dépendance, banc, replay ou rendu n’a été relancé. Aucun calcul numérique ne relève de cette production : le rôle6 teste les banques nouvelles sélectionnées par le coordinateur.

## Résultat mathématique livré

La signature finale principale est :

```lean
GoldbachRound16.Margin.large_prime_margin {p : ℕ} (hp : 13 ≤ p) :
  1 / 144 ≤ (harmonic (p - 1) : ℝ) *
    (((p : ℝ) - 2) / ((p : ℝ) - 1)) - Real.log (p : ℝ)
```

`harmonic` est le nombre harmonique rationnel réel de mathlib, pas un paramètre libre. La primalité de p n’est pas nécessaire pour cette partie. Le module prouve d’abord `1/4 ≤ harmonic n − log(n+1)` pour n≥1, en utilisant la monotonie stricte de `Real.eulerMascheroniSeq` et une certification indépendante de log2<3/4.

Pour p≥13, la preuve ne postule pas la monotonie d’une nouvelle fonction g. Elle applique `log(p/13)≤p/13−1`, puis log13<8/3, et obtient `logp≤8/3+(p−13)/13`. Ce majorant tangent est suffisant : le coefficient de p dans `((p−2)/4−logp)−(p−1)/144` est positif, et la borne s’annule en p13. La multiplication par p−2 et la division par p−1 gardent les gardes de signe explicitement prouvées.

Les bornes logarithmiques strictes livrées sont log3<9/8, log5<2, log7<2, log11<5/2, ainsi que log2<3/4 et log13<8/3. Elles sont certifiées par des sommes finies positives de la série exponentielle puis `norm_num`, sans approximation flottante, oracle numérique ou `native_decide`. Les sommes comportent respectivement7,4,6,7,4 et7 termes. Avec les minorants source2541/2048,2541/1024,847/256,2541/640 déjà sélectionnés pour p3,5,7,11, ces bornes donnent strictement plus que1/144. Le rôle3 garde la responsabilité de dériver ces minorants du vrai `GoldbachRound11.singularSeries`, du produit réel C2 et de son enclosure acquise, puis de brancher les quatre cas.

L’interface d’import est `LeastMissingPrimeMargin`, namespace `GoldbachRound16.Margin`. Les signatures des petites bornes sont `log_three_lt_nine_eighths`, `log_five_lt_two`, `log_seven_lt_two`, `log_eleven_lt_five_halves`. Le rôle3 a reçu la signature exacte et le chemin du `.olean` dès la compilation terminée. Aucune hypothèse équivalente à A7 n’est ajoutée au module.

## Compilation observée et conservation des essais

Une seule invocation nouvelle a été exécutée par `round16/role4/compile_new.ps1 -Attempt 1`, avec Lean4.15.0 et les huit bibliothèques construites du cache mathlib9837ca9d65d9de6fad1ef4381750ca688774e608. La source a été copiée dans `attempt1.lean` avant l’exécution. Début2026-10-02T18:25:45.3191902Z ; fin2026-10-02T18:26:10.3129467Z. Le processus a renvoyé exit0, sans erreur ni warning. La source finale est identique au snapshot de cette tentative. Aucune correction après ce PASS et aucune recompilation de ce producteur ne sont effectuées.

Le module contient9 théorèmes et0 définition nouvelle. Les neuf sorties `#print axioms` donnent uniquement `[propext, Classical.choice, Quot.sound]`. Le scan lexical des tokens interdits `sorry`, `admit`, déclaration `axiom`, `native_decide` renvoie0 dans la source. Aucun échec réel Lean n’a eu lieu dans ce rôle : il n’existe donc aucun faux diagnostic du mur de parité ni journal d’échec inventé. Le Juge indépendant conserve la responsabilité de compiler/auditer les nouveaux certificats de la boucle et d’en vérifier la portée.

| Production | SHA256 |
|---|---|
| LeastMissingPrimeMargin.lean / attempt1.lean | e1dbd4f8a68b433c4641c90d6eb12366e7084b0d8b7b7b045b8b11ebd41e6b4a |
| LeastMissingPrimeMargin.olean | b06c8bc51d8d097766f47e1ec553b48a3bde67daa08c9a0ece1ff901e76f0595 |
| compile_new.ps1 | a565f42b2b7d4b9b048dfb19e09feb80861d7e629729128ab7d29c5caa388389 |
| attempt1.log | 91504945ea420cb4a870d7c98ae5d2d0ae9f3d80937a6a848ed8ceababc02199 |
| attempt1_receipt.json | 21e73415ac9f0ef23bdda5ba1c29d37088c2fe436f0965d434207398562956f3 |

Le reçu lie également le binaire Lean SHA8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08. La preuve fournie ne dépend d’aucun `.olean` ancien de Goldbach ; elle importe seulement mathlib. Le vrai produit source demeure défini dans l’input immuable du rôle3, avec le raccord explicite à ce nouveau module.

## Limite exacte et résultat exploitable

Le résultat est une composante quantitative nouvelle de A7 et non une identité tautologique conditionnée par la marge voulue. Il fournit à l’agent3 un théorème pour tous p≥13 et des petits logarithmes certifiés. Il ne prouve pas à lui seul que le produit singulier est au-dessus de la quantité harmonique ; convergence, comparaison de la queue réelle et facteurs locaux appartiennent au module3. Il n’est pas un certificat isolé de S(N)−logp0≥1/144 et ne transforme pas une capacité pointwise favorable en masse disponible.

Même après un raccord complet A7, le vrai signe source A9 suppose les inputs analytiques acquis dans leur domaine u≥10^24, les gardes physiques et les deux axes premiers. N=10^8 reste hors onset. Aucun signe du kernel fini ni crédit de capacité réutilisé n’est postulé ici. L’incidence OR, la covariance corrigée et la comparaison globale après union restent non estimées. Le ledger entier, les puissances propres raw, fronts, originalQ et unités restent sous contrôle du coordinateur.

**Score :** 0. **Result :** `HARMONIC_ANCHOR_MARGIN_COMPILED_FIRST_ATTEMPT`, `NINE_AUXILIARY_THEOREMS`, `STANDARD_AXIOMS_ONLY`, `ACTUAL_SINGULAR_SERIES_CONNECTION_ASSIGNED_TO_ROLE3`, `GLOBAL_CAPACITY_UNESTIMATED`, `VICTORY_FALSE`. **Code_ref :** `round16/role4/LeastMissingPrimeMargin.lean`.
