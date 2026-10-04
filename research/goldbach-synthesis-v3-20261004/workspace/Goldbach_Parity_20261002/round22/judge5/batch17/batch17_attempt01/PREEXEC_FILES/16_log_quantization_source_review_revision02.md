# Log32 → enveloppe du coefficient : revue indépendante SOURCE52

ROLE5, auteur ROLE3 distinct ; SOURCE/PAPER seulement. Aucun parseur Lean, compilation, import Python, calcul de valeurs, builder ou banc. **Aucun déficit logique ou API précis détecté**, sans PASS anticipé. La paire contient52 déclarations : RationalLogQuantization38=23thm15defs et QuantizedLambdaEnvelope14=9thm5defs, soit32thm20defs52prints qualifiés. Pas de sorry/admit/axiom déclaré/unsafe/native_decide dans les corps lus. Axiomes transitifs et élaboration restent inconnus jusqu'à une compilation autorisée.

Racine : `D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002\round22\role3\log_quantization_source22\revision02`.

| Fichier | SHA256 | Lecture propre |
|---|---|---|
| RationalLogQuantization22.lean | 9e59eb6b8aa4efcb5cc6cdc27d7d7a7d24517986fcd1ad2b4413b97c0efc1fb0 | FULL87a11a |
| QuantizedLambdaEnvelope22.lean | 526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331 | FULLa87644 |
| dependency_contract22.md | cdb1b8510c13fe6ff69b6ed510df90335a831cef0181182c050c1781965fe91f | FULL587fd9 |
| source_manifest22.json | 3d0af8eefbb29fd902bf3b1b86b4b15bce7280cbb262b1159486165ae2fd6a74 | FULL587fd9 |
| read_receipts22.json | de4b33633a9e66471ed7a3d00c63dab2e522af6d356bc0968115076c3b29bcf9 | FULLc127c0 |

La sortie ae4a74 tronquée est exclue comme FULL. Le premier appel e7369c n'affichait que les noms des APIs à cause de l'énumération des ranges ; ce n'est pas une lecture de leurs lignes. Correction propre TARGETED054dec : Log/Deriv272–299, InfiniteSum/NatInt197–234, InfiniteSum/Order30–61, Nat/Log208–234. TARGETEDb3b8e6 : Nat/Log106–150, SpecificLimits/Basic278–300, VonMangoldt58–86, Prime/Defs254–284, Order/Floor642–680. Ces API réelles correspondent aux signatures utilisées, notamment HasSum de log, décalage de queue, ordre des sommes, série géométrique, floor et minFac. Pas de FULL mathématique de tous les imports ni de fermeture préparée.

## Constructeur rationnel et précision

Le HasSum réel de log(1+z)−log(1−z) fournit la série. Pour0≤z≤1/3, le terme j+32 est borné par `(2/65)*3^(-65)*(1/9)^j`. Le facteur de somme géométrique est9/8 ; le reste fermé est donc exactement `R32=9/(4*65*3^65)`, positif, sans reste supposé. `hasSum_nat_add_iff'` a bien l'orientation utilisée pour soustraire la somme finie.

Les seules gardes de précision sont2≤p≤100000000. Nat.log2 paie k≤26 et2^k≤p<2^(k+1). Le dénominateur p+2^k est positif ; z=(p−2^k)/(p+2^k) appartient à[0,1/3]. L'identité logarithmique est dérivée avec tous les nonzeros ; la boîte de log2 vient elle aussi de la série àz=1/3. Width=(k+1)R32≤27R32≤1/S, S=2^58. La SOURCE prouve cette borne suffisante non stricte, pas la borne documentaire plus forte2^(-96) ; la garde native stricte reste distincte.

nearestEven utilise floor rationnel, écart fractionnaire et parité exacte au tie. La preuve erreur≤1/2 couvre toutes les branches, y compris les deux choix au tie. Clamp[0,32S] contracte la distance à Slogp parce que la vraie borne0≤logp≤32 est construite. La somme des deux erreurs donne |logp−A32/S|≤1/S. Aucun hPrecision, intervalle, epsilon ou valeur de log n'est fourni en prémisse. Les quatre monotonies révisées sont explicites et mathématiquement correctes.

La définition rationnelle correspond sur papier au midpoint puis divmod/tie-to-even/clamp du modèle80718ee9… relu FULL0f013d. Une équivalence des réalisations common-denominator, mots/carries/divmod et enregistrements natifs reste à démontrer ; le texte SOURCE n'est pas leur exécution ni leur certificat.

## Lambda, coefficient et domaine

Le second module utilise précisément IsPrimePow/minFac de la véritable vonMangoldt. Ces branches incluent toutes les puissances premières ; n=0,1 appartiennent à la branche zéro. minFac_prime et minFac_le dérivent2≤minFac≤n≤100000000 dans la branche PP. Les poids quantifiés et véritables ont effectivement la borne32, et leur précision vient du constructeur du premier module.

La décomposition `xy−uv=x(y−v)+v(x−u)` donne64/S par produit puisque0≤x,v≤32 ; le terme1/S² n'est même pas nécessaire à cette preuve. Somme sur N+1 termes, N≤100000000, puis cast/somme/division exacte donnent `|C_N−I_N/S²|≤(N+1)(64/S+1/S²)`. Aucune minoration, coefficient cible ou borne finale n'est une prémisse. errorEnvelope est continu sur le **paramètre formel s>0** ; la précision/coefficient démontrés dans SOURCE concernent uniquement le S fixé2^58. Ne pas transformer cette continuité en une précision valable pour toute échelle. La garde entière du tau est une proposition fermée à constantes fixes avec norm_num, jamais évaluée par ROLE5.

Cette enveloppe ne dépend pas d'anciens modules de projection ou de leurs oleans ; seule la dépendance locale RationalLogQuantization est requise. La source est autonome vis-à-vis de Mellin/full-M/H1. Elle ne paie pas une réalisation native : égalité canonique de chaque enregistrement A32, classification minFac/PP complète, NTT/CRT/aliases, dépassements et calcul réel coefficientN restent ouverts. Les cinq échantillons du futur guard ne couvrent pas tout le catalogue. D_N, PP/frontière, H1 global et WIN ne découlent pas de cette approximation finie. Aucune préparation de lot suivant n'est autorisée par ce rapport.
