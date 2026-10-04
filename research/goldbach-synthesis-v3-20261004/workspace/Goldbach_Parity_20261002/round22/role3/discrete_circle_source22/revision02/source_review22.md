# Discret : révision SOURCE 02 de l'ordre des sommes

Statut `SOURCE_ONLY_NOT_PREPARED_NOT_COMPILED`. Aucun compilateur, probe, parser Python, import runtime, banc, builder ou gate n'a été lancé pour cette révision. Les 29 déclarations, leurs noms, énoncés, domaines et 29 prints sont conservés ; neuf définitions et vingt théorèmes. Le fichier original SHA `2a964deed343671d87b518b4da956cd36ad33fd6965f1feb69e5d3739ef0e696` reste immuable.

ROLE5 a signalé un risque technique SOURCE dans `discretePartial_square_expansion` : la simplification simultanée par `Finset.sum_mul` et `Finset.mul_sum` peut privilégier l'autre ordre de distribution et laisser les deux indices transposés. Ce n'est pas un FAIL Lean observé pour ce module, qui n'a jamais été compilé. La validité mathématique de l'identité finie n'est pas remise en cause par ce motif.

La nouvelle preuve fixe explicitement l'ordre de l'expansion. Après `unfold discreteHeatPartial` et `pow_two`, `Finset.sum_mul_sum` produit la somme sur m puis la somme sur n du produit terme(m)*terme(n). `Finset.sum_product` déroule le membre droit exactement dans le même ordre. `simp_rw [Finset.sum_mul]` distribue ensuite le caractère commun sur ces deux sommes sans réordonner leurs indices. Aucune nouvelle hypothèse d'orthogonalité ou de coefficient n'est ajoutée. Il n'est plus nécessaire de faire dépendre cette expansion du choix du simplificateur entre deux règles concurrentes, ni d'utiliser une commutation finale pour le réparer.

L'API réelle lue dans le cache mathlib4.15 est `Mathlib/Algebra/BigOperators/Ring.lean`, lignes 42–50 :

```lean
lemma sum_mul (s : Finset ι) (f : ι → α) (a : α) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
lemma sum_mul_sum {κ : Type*} (s : Finset ι) (t : Finset κ)
    (f : ι → α) (g : κ → α) :
    (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j
```

Son import explicite est ajouté. A0 reste `max N (2*M-N) < K`, avec M≥N pour CIRCLE ; tous les poids demeurent les vrais `ArithmeticFunction.vonMangoldt`, y compris les puissances premières. Les caractères restent les exponentielles complexes concrètes. Aucun autre corps de preuve n'est modifié. Cette source conserve les dettes d'élaboration et de contrôle indépendant des 29 déclarations ; elle ne reçoit aucun PASS anticipé ni aucune estimation de D_N.

Scopes : ancienne source FULL3045d4 ; API Ring TARGETED9–74 ea5a24, SHA `0e11d9b338fa211ed86b6692fa08b4c6cf47033aaf8bc14a055d6e8976dc5d10` ; recherche corrigée 1d4c60. Le premier chemin deviné `Ring/Finset.lean` était absent (e755b8), ce qui est une erreur de lecture de chemin et pas une erreur Lean. Le `rg` final d'ea5a24 n'a pas trouvé les déclarations to_additive dans Group/Finset ; la lecture Ring indiquée a néanmoins été entièrement affichée. Les lectures antérieures de `sum_product` restent liées dans le reçu original. La prochaine étape est une revue SOURCE indépendante, puis seulement une préparation et une gate ROOT distinctes si le coordinateur les autorise.
