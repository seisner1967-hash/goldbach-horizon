# FINAL 4 — Boucle 17 : racines réelles, troncature et perte de collisions

Statut : **PASS auxiliaire partiel**, `score = 0`, `victory = false`. Quatre nouveaux modules Lean compilent sans erreur, avertissement, `sorry`, `admit`, nouvel axiome ou `native_decide`. Le résultat quantitatif certifié est une minoration du **vrai** `actualG` par un produit fini explicite, sous un input analytique indépendant sur la somme logarithmique des premiers. La borne source C4 complète, C6 et le paiement global ne sont pas certifiés par ces modules.

Le rapport d’idéation FINAL 2 est immuable : `agent2_capacity_incidence.md`, SHA-256 `2c3b2dfadb507925b0fdc92a69b5174353f8f93ba2fc188175dadf05b38ad8d7`. Le noyau `FourFormRoots` est figé depuis l’essai 8. Les trois modules ultérieurs ont été ajoutés séparément ; aucune source historique n’a été modifiée ou reconstruite.

Mechanism: Construire les racines des quatre formes effectives dans `ZMod ℓ`, raccorder le polynôme entier, puis appliquer le moment fini et Markov au `G` réellement construit par Selberg ; payer localement les collisions par un produit explicite.

Hypothesis: Pour la borne en quatre racines, `e.Coprime N` et `p0.Coprime N` ; pour la troncature, absence de saturation sur les vrais premiers ≤ z, `y ≤ z`, `log z ≥ 32`, `32 log y ≤ log z` et l’input analytique `Σ_{p≤y} log p / p ≤ 2 + 2 log y` ; pour le raccord à Δ naturel, `1 ≤ p0 ≤ e`.

Observable: Racines, cardinal ρ, densité ρ/ℓ, produit entier, cellule rugueuse, moment fini, support des sous-ensembles, vraie masse `actualG` et produit de perte sur les premiers divisant Δ sont définis, puis reliés par les théorèmes compilés.

Conflicts: Aucune disponibilité première, densité de couples, hypothèse `G ≥ cible`, C4 ou C6 n’est posée. La somme analytique sur les premiers, Mertens, le prix en totient, CRT +1, les sommes physiques pondérées et les capacités globales demeurent hors de la certification actuelle.

## Objets et raccord arithmétique

Le namespace `GoldbachRound17.FourFormRoots` définit, pour tout modulus naturel ℓ,

\[
F_\ell(x)=x(N-ex)(N-x)(N-p_0x),\qquad
\rho_\ell=\#\{x\in\mathbf Z/\ell\mathbf Z:F_\ell(x)=0\},\qquad
g_\ell=\rho_\ell/\ell.
\]

Les racines sont le filtre d’une véritable énumération des résidus `range ℓ`, et non une variable libre. Pour ℓ premier, cette énumération est prouvée égale à `Finset.univ`. Les définitions restent totales sur ℕ ; les théorèmes de corps portent une instance `Fact ℓ.Prime`. Le cas ℓ = 0 n’est pas utilisé par le crible.

Les théorèmes `rho_lower`, `rho_le_modulus`, `rho_le_four` et `rho_bounds` donnent

\[
1\le\rho_\ell\le\min(4,\ell)
\]

sous les deux gardes de coprimalité. Elles empêchent qu’une forme linéaire soit identiquement nulle : si ℓ divise son coefficient e ou p0, elle ne divise pas N, donc cette forme n’ajoute aucune racine. Les quatre candidats sont `0`, `N`, `N/e` et `N/p0` dans le corps résiduel ; un coefficient nul est traité avant toute division.

Le produit de collisions dans le corps est

\[
N e p_0(e-1)(e-p_0)(p_0-1).
\]

`rho_eq_four_of_collision_nonzero` prouve que son absence d’annulation rend les quatre racines distinctes. `natDelta_cast` raccorde ce produit à

\[
\Delta=N e p_0(e-1)(e-p_0)(p_0-1)\in\mathbf N
\]

sous `1 ≤ p0` et `p0 ≤ e`, qui conservent exactement les soustractions naturelles. `rho_eq_four_of_not_dvd_delta` en déduit ρ = 4 hors des diviseurs premiers de Δ. Aucun résultat de norme générique ou modèle constant ne remplace ce calcul.

Si ℓ divise N, les gardes de coprimalité impliquent exactement `actualRoots = {0}` et ρ = 1. Une saturation ρ = ℓ donne `actualRoots = univ` et donc `F_ℓ(x) = 0` pour chaque résidu. Le cas modulo 3 est certifié pour `N = 1` dans `ZMod 3` et `p0 = 3` : e de classe 2 donne toutes les racines et ρ = 3 ; e de classe 0 ou 1 donne `{0, 1}` et ρ = 2. Le code ne généralise pas ces branches à un p0 arbitraire.

Le polynôme entier `integerForm N e p0 q` conserve les soustractions dans ℤ :

\[
F(q)=q(N-eq)(N-q)(N-p_0q)\in\mathbf Z.
\]

`integerForm_cast` prouve que son image résiduelle est `actualForm`. `integerForm_dvd_iff` prouve l’équivalence entre ℓ divisant ce polynôme entier et son annulation résiduelle. Enfin, `saturation_roughCell_empty` donne, pour **tout** ensemble fini J et tout ensemble P contenant un premier saturé,

\[
\{q\in J:\forall\ell\in P,\ \ell\nmid F(q)\}=\varnothing.
\]

Ce résultat ne requiert ni primalité de q ni primalité des trois autres formes. Il s’applique à la cellule rugueuse exacte. Il ne prouve aucune exclusion de la mesure `rawLambda_N` des puissances propres, qui reste au complément.

## Moment et troncature certifiés

Le DAG est `FourFormRoots` → `SelbergFourForms` FINAL 3, puis `FourFormTruncation` qui importe également `PowersetMoment`. Le module de collisions importe la troncature. Le source et l’olean FINAL 3 sont lus et liés par empreinte ; ils ne sont pas reconstruits par le rôle 4.

Pour les vrais premiers P_y ≤ y, on pose

\[
h_p=\frac{g_p}{1-g_p},\quad W_s=\prod_{p\in s}h_p,\quad
Z_y=\prod_{p\in P_y}(1+h_p),\quad L_s=\sum_{p\in s}\log p.
\]

`PowersetMoment.total_weight` dérive `Σ_s W_s = Z_y`. `weighted_moment` dérive, par induction sur l’ensemble fini et sans loi probabiliste postulée,

\[
\sum_{s\subseteq P_y}W_sL_s
=Z_y\sum_{p\in P_y}\frac{h_p}{1+h_p}\log p.
\]

`actualH_ratio` identifie ce quotient à la véritable densité g_p lorsque ρ_p < p. `actual_weighted_moment` dérive donc le moment exact `Z_y Σ g_p log p`.

`cutoff_markov` conserve tous les sous-ensembles dont le produit entier excède z. Pour chacun d’eux, `log(prod s) ≥ log z` ; la somme pondérée de cette queue est contrôlée par le moment. Si le moment est au plus `Z_y log z / 2`, la masse sous le seuil est au moins `Z_y / 2`. Le code prouve l’identité de log du produit et le passage à cette inégalité ; il ne supprime aucune queue par convention.

`G_mono_support` dérive la monotonie du véritable `G` par inclusion des supports et positivité des produits h. Les sous-ensembles de P_y ayant produit ≤ z sont un sous-support de `actualG N e p0 z`, qui utilise tous les premiers ≤ z. Ainsi `actual_G_half_euler_of_log_moment` certifie

\[
\sum_{p\le y}g_p\log p\le\frac{\log z}{2}
\quad\Longrightarrow\quad
\frac{Z_y}{2}\le G_{\rm actual}(z).
\]

Le wrapper quantitatif ne s’arrête pas à une prémisse équivalente à cette minoration. `actual_density_log_sum_le_four` utilise les racines réellement prouvées et les coprimalités pour dériver

\[
\sum_{p\le y}g_p\log p\le4\sum_{p\le y}\frac{\log p}{p}.
\]

`actual_G_half_euler_of_prime_log_sum` garde l’input analytique indépendant

\[
\sum_{p\le y}\frac{\log p}{p}\le2+2\log y,
\quad \log z\ge32,\quad32\log y\le\log z.
\]

Il dérive ensuite `4 Σ log p/p ≤ 8 + 8 log y ≤ log z/2`, puis `Z_y/2 ≤ actualG`. Cet input de somme première n’a pas été prouvé en Lean dans cette mission. Dans la démonstration écrite source, il suit de θ(x) < 2x, pour x > 0, par sommation partielle ; cela n’est pas un axiome ajouté au module.

## Perte locale de collisions certifiée

`FourFormCollisionLoss` définit

\[
b_p=1-1/p,\quad P(y)=\prod_{p\le y}b_p^{-1},\quad
L_\Delta(y)=\prod_{p\le y}
\begin{cases}b_p^3,&p\mid\Delta,\\1,&p\nmid\Delta.\end{cases}
\]

Ces produits utilisent les mêmes vrais premiers que `actualG`. Pour un premier divisant Δ, ρ_p ≥ 1 donne `(1-g_p)^{-1} ≥ b_p^{-1}`. Pour un premier ne divisant pas Δ, ρ_p = 4 et l’inégalité de Bernoulli `1 - 4/p ≤ (1 - 1/p)^4` donnent `(1-g_p)^{-1} ≥ b_p^{-4}`. La non-saturation assure la positivité des dénominateurs. `collision_factor_le` prouve ces deux branches ; `actualEuler_collision_loss` les multiplie et dérive

\[
P(y)^4L_\Delta(y)\le Z_y.
\]

Le théorème final `actualG_collision_loss_half` combine ce paiement effectif avec la troncature et donne

\[
\boxed{\quad G_{\rm actual}(z)\ge\tfrac12 P(y)^4L_\Delta(y)\quad}
\]

sous les gardes précises ci-dessus. Il n’assume ni le produit de perte désiré, ni un minorant libre de G. Le coût en collisions est explicite ; les facteurs locaux p divisant N, e, e − 1, e − p0 ou p0 sont conservés dans Δ. Les deux coprimalités restent présentes dans le wrapper final qui contrôle le moment.

La transformation écrite `L_Δ(y) ≥ (φ(Δ)/Δ)^3`, le minorant de Mertens `P(y) ≥ log y`, le prix analytique de `Δ/φ(Δ)` et l’adaptation des seuils naturels aux puissances réelles de N **ne sont pas certifiés ici**. Le théorème final porte sur les produits finis effectifs et garde l’input indépendant de somme première. Il ne doit pas être étiqueté « C4 source entièrement Lean ».

## Vérification et gel

Lean 4.15.0 utilise le cache mathlib q356 et les bibliothèques aesop, batteries, importGraph, LeanSearchClient, mathlib, plausible, proofwidgets et Qq. Le rôle 4 a lancé 16 véritables compilations : 5 sorties 0 et 11 sorties 1. Les sorties 0 finales sont les essais 8, 11, 13 et 16 ; l’essai 15 compilait avec un avertissement de style, corrigé à l’essai 16. Il n’y a eu aucun ancien module reconstruit, aucune ancienne banque rejouée et aucun rendu PDF lancé.

Chaque invocation réelle conserve `attemptNN_source.lean.txt`, `attemptNN.log`, commande, code de sortie, empreinte, et olean lorsqu’il existe. Les échecs sont conservés avant correction : 1–7 concernent les instances ZMod, les casts, les divisions et les preuves concrètes modulo 3 ; 9–10 concernent le cast du produit naturel et une lambda du logarithme ; 12 concerne deux réécritures techniques du raccord au moment ; 14 concerne des normalisations de fractions et Bernoulli. Les `sorryAx` de récupération d’élaboration dans certains journaux d’échec ne sont pas dissimulés ; aucun n’apparaît dans les quatre journaux finaux. Une commande shell avec un chemin Python mal saisi n’a pas lancé Lean et n’est pas comptée comme compilation.

Le compte des **nouveaux** objets est 4 modules, 51 théorèmes, 17 définitions et 1 instance nommée. Les 69 déclarations ont chacune un `#print axioms` dans leur module. Les listes finales ne contiennent que `propext`, `Classical.choice` et `Quot.sound`. Les 42 théorèmes et 23 définitions du module FINAL 3 importé ne sont pas recomptés dans ce total ; aucun objet historique importé ne l’est non plus.

| Module final | Essai | SHA-256 source | SHA-256 olean |
|---|---:|---|---|
| `FourFormRoots` | 8 | `49cbf93fd8eb9aa75236419d5d7b95e1841d67571865171115ffbbdfcb71e9fa` | `4a13fc20feabfd5ff552f5dbd18c99c6b66bcfe1a65a3f44fff555417d7b4021` |
| `PowersetMoment` | 11 | `971f351decef7e78112ec940c5ee553806abecccaf19440a4d661881c4ae188d` | `f1b9c19267d9c6df430156f3731613bd1fbcf58bf50e626417a74dc8449f1905` |
| `FourFormTruncation` | 13 | `577ff585207e72bf5d31121743fc218effc91eb8a460cef9fa9ee2e05a3996e0` | `340667c515537e2d5501e19329c4becb39cef6989699439107f85a4ec520dbc1` |
| `FourFormCollisionLoss` | 16 | `000cade7cac3a1c9472a2fd465e992de71a49c6ad65ae85635726d196392d9a5` | `e8f5c07ef6225671165e1fb942d4f0c39e3540ee8d1a3ee1e21d0205e10a3091` |

La dépendance FINAL 3 `SelbergFourForms.lean` est liée par SHA-256 `b1b658aa92f8e02cef29667e9e60b763ca3ef57bb25dcbc8aa9c50ba33591ce1` ; son olean a SHA-256 `9639c1f7ae9eb03d07c1de2fd79cdea4dd503d29716e5de3adb4085de21fc46c`. Le reçu `role4/final_receipt.json` lie ce rapport, tous les sources, snapshots, logs, oleans et scripts propres, et vérifie les déclarations et axiomes. La protection des 799 archives appartient au préflight root ; le rôle 4 a écrit uniquement dans son ownership.

## Contrat fini neuf et obligations restantes

Le root a sélectionné une annexe numérique distincte pour N = 10^8, z = 100 et les 16 cœurs non saturés du nouveau banc rough 17. Aucun de ses 33 bindings FINAL 6 ne doit être modifié. Pour chaque cœur, P = {2, 3, 5, 7} et ses 16 sous-ensembles doivent conserver les vrais ρ, g, h, produits, poids rationnels et queue entière. Les égalités à tester sont `Σ W = Z`, le coefficient rationnel de chaque `log p` dans le moment égal à `Z g_p`, `G_P + Tail = Z` et `G_P ≤ G_actual`. La condition de demi-moment doit être mesurée, avec statut FALSE conservé lorsqu’elle échoue. Aucune borne C4 ou C6 source n’est appliquée à cette fenêtre finie. Ce banc et son rejeu relèvent du rôle 6 ; ils ne sont pas des compilations ou tests exécutés par le rôle 4.

La source asymptotique commence à u = log N ≥ 10^24. Le N fini est exploratoire. Le reste T_S, qui porte les branches à petit facteur, et T_A après consommation unique des ressources restent non payés. La partition A/R/S demeure exacte ; une ressource non première n’est jamais identifiée à une ressource rugueuse. Ni ces modules ni le banc fini ne donnent une disponibilité de partenaires ou une capacité globale suffisante.

Le ledger conserve e = 1, les cœurs premiers et leur Λ(e), rang 2 et autres couches, les deux signes, les puissances propres `rawLambda_N`, le vrai U4/sourceBracket, Q original, k = 1, `wholeU_a`, c = 1, S(cN), le principal, les longs, les faces et les erreurs e. P5 reste sur le bloc entier avant retraits. Aucun coût local n’est payé deux fois, aucun parent physique réutilisé n’est autorisé par ces preuves. CRT +1 et son coût total, C6 pondéré et son onset, T_S/T_A et la cible `D_N ≤ N/(256 u log u)` restent ouverts.

Références primaires du calcul source écrit, non assimilées à des imports Lean : [Ford, notes de crible 2023](https://ford126.web.illinois.edu/sieve2023.pdf), PDF pages 42–44, pages imprimées 43–45, théorème 4.1 et formules (4.4)/(4.5) ; [Rosser–Schoenfeld 1962](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf), PDF pages 7–8, pages imprimées 71–72, θ(x) < 1.01624 x pour x > 0, et (3.42) pour n ≥ 3 ; [notice DOI primaire](https://doi.org/10.1215/ijm/1255631807). La garde de θ couvre donc θ(x) < 2x pour tout x > 0 ; le théorème de totient garde n ≥ 3 et n’est pas importé comme axiome.

**FINAL terminé. Aucun Win ni NoGo global.**
