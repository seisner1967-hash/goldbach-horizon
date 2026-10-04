# Raccord G0 géométrique — résultats auteur figés

Les quatre modules ont réellement compilé sous Lean4.15, chacun lors de sa dernière invocation autorisée, sans placeholder source et avec audits limités aux axiomes standards propext, Classical.choice et Quot.sound. Les sources et olean restent immuables. Le Juge indépendant doit encore déterminer leur crédit officiel ; aucune victoire Goldbach n’est attribuée à G0.

Pour y>0 et m∈ℤ non nul, on définit le noyau original par

K(y,m,x,n)=y^(3/2)/(((mx+n)²+(my)²)^(3/2)).

L’intégrale I_Q est réellement celle de la somme sur n∈[−Q,Q] et x∈[0,1]. L’intégrale I_∞ est celle de la série sur tous les entiers. Avec q=natAbs m, a=qy et H_a(u)=u/√(u²+a²), les conclusions compilées sont :

1. I_Q=y^(3/2)/(qa²)·(Σ_{u=Q+1}^{Q+q}H_a(u)−Σ_{u=−Q}^{−Q+q−1}H_a(u)). La substitution affine signée et la bijection n↦−n paient le cas m<0.
2. I_∞=2/(q²√y). La convergence locale, la continuité de la périodisation, la sommabilité des intégrales des normes et l’échange infini sont prouvés ; le recouvrement signé est traité par périodicité exacte.
3. Si Q>q, 0≤I_∞−I_Q≤y^(3/2)/(Q−q)². Cette erreur réelle est exprimée par les déficits positifs des deux bords. Le facteur q de recouvrement et le jacobien sont conservés.
4. L’enveloppe réelle E(y,T,q)=y√y/(T−q)² est continue conjointement en (y,T) sur T>q. Son évaluation à T=(Q:ℝ) est l’enveloppe précédente, et y√y=y^(3/2) pour y>0.

| Module final | Théorèmes | Définitions | Audits | Invocation finale réelle UTC |
|---|---:|---:|---:|---|
| EpsteinKernel22 | 28 | 5 | 33 | 07:14:47.195648–07:15:17.486606, exit0 |
| EpsteinFinite22 | 14 | 4 | 18 | 07:35:44.925627–07:36:07.068572, exit0 |
| EpsteinUnfold22 | 16 | 3 | 19 | 08:29:04.716790–08:29:29.900322, exit0 |
| EpsteinTail22 | 11 | 3 | 14 | 08:35:09.799051–08:35:31.051697, exit0 |
| Total auteur | 69 | 15 | 84 | 4 sources finales |

Chaque invocation possède PREEXEC, START, commande, log, exit, POSTEXEC, reçu et captures neufs. Les échecs antérieurs Kernel1, Finite1–2 et Unfold1–3 sont conservés ; ils concernent des API ou des normalisations de coercions, et ne sont pas présentés comme des réfutations analytiques ou une obstruction de parité. Aucune dépendance PASS n’a été recompilée par son auteur pour assembler le module suivant. Le catalogue G0_final_catalog.json lie les sources, olean, logs, reçus et manifests finals par SHA256.

Le banc informatif G0 unique de ROLE6, accepté par root, comportait 24cas et 295198certificats de carrés. ROLE3 n’a exécuté aucun calcul Python, probe Lean ou ancien rejeu de PASS. Le banc est auxiliaire géométrique ; il ne valide aucune contribution des premiers à N=10^8.

Le raccord ne traite ni la somme complète en m du cusp0, ni une identité de Weil, les zéros complets, la diffusion, Mellin, la chaleur, le coefficientN ou D_N. Ces obligations restent distinctes. Il n’utilise aucune forme bilinéaire arithmétique, crible, inversion de Möbius, Vaughan ou estimation scalaire de restes de progressions. La garde source u=logN≥10^24 n’est pas confondue avec N=10^8. Aucune cible D_N n’est créditée.
