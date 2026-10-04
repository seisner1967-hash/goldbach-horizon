# Chemins des certificats stockés — préparation, aucun nouveau calcul

Les chemins ci-dessous désignent les certificats déjà écrits dans les deux sorties canoniques. Les variables `<mask>` et `<m>` sont les clés littérales de leurs catalogues ; `<i>` est l'indice de liste. Cette liste est déduite de la topologie des producteurs gelés, sans relancer un producteur, un kernel ou un signe.

## TypeII : 98 positions stockées

- `/R1_complete_column_sign_certificate/<mask>/operator_l1/sign_certificate` : 4.
- `/functionals_exact/<weight>/beta_primitive/sign_certificate` : 4.
- `/functionals_exact/<weight>/unit_primitives/<mask>/sign_certificate` : 16.
- `/functionals_exact/<weight>/by_mask/<mask>/reference/sign_certificate` : 16.
- `/functionals_exact/<weight>/by_mask/<mask>/z_functional/sign_certificate` : 16.
- `/functionals_exact/<weight>/by_mask/<mask>/normalized_x_over_A/sign_certificate` : 16.
- `/prices_by_weight/<weight>/E91/<h>/sign_certificate` : 8.
- `/prices_by_weight/<weight>/L11/<scope>/sign_certificate` : 8.
- `/R2_R7_R8_by_scope/<scope>/finite_budget_comparison/sign_certificate` : 2.
- `/local_promotion_falsifiers/<i>/sign_certificate` : 2.
- `/R9_R10_details/<scope>/theta_removed_class_primitive/sign_certificate` : 2.
- `/R9_R10_details/<scope>/raw_removed_class_primitive/sign_certificate` : 2.
- `/R9_R10_details/<scope>/raw_minus_theta_price/sign_certificate` : 2.

`weight ∈ {theta, II, II_raw, raw}`, `mask ∈ {0:39,0:429,91:39,91:429}`, `h ∈ {39,429}`, `scope ∈ {0,91}`. Les deux comparaisons reprises dans la liste des falsifiers sont deux positions stockées supplémentaires, pas deux nouveaux témoins indépendants. Observation root déjà reçue : 40 POS, 25 NEG, 33 ZERO.

## SS : 222 positions attendues de la topologie effectivement atteinte

- `/new_selected_kernel_profiles/<m>/weighted_raw_C_sign_certificate` : 54.
- `/new_selected_kernel_profiles/<m>/C_sign_certificate` : 54.
- `/new_selected_kernel_profiles/<m>/W_kernel_sign_certificate` : 54.
- `/selected_theta_axes_signs/<m>/sign_certificate` : 40.
- `/physical_union/reciprocal_m1_resources_counted_once/<i>/capacity_positive_part_sign_certificate` : 14.
- `/selected_measures/<measure>/sign_certificate` : 6.

Les six mesures sont `signed_SS_theta`, `positive_debt_SS_theta`, `SS_raw_proper_power_signed`, `unique_m1_capacity_measured`, `partial_SS_minus_measured_m1`, `unique_physical_union_signed`. Le nombre 222 provient des tailles effectives annoncées et du code gelé ; sa lecture JSON exacte et sa distribution POS/NEG/ZERO restent à l'inspection indépendante, puis au manifeste final. Aucune distribution de signes n'est présumée.

Les racines, poids rationnels, CRT et identités Selberg sont des données exactes supplémentaires ; leurs scalaires ne sont pas artificiellement ajoutés au décompte de certificats de signe. Les noyaux absents restent absents : aucun `kernel_ref` nul n'est inventé pour un axe littéral non évalué.
