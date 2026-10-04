# Log32 → enveloppe du coefficient — révision03 SOURCE distincte

Statut SOURCE_ONLY_NOT_COMPILED_REVISION03. Deux modules, 52 déclarations (38+14), 20 définitions et32 théorèmes, chacun avec #print axioms qualifié. Les 52 en-têtes/domaines, les20 corps de définitions et les52 prints sont textuellement identiques à revision02. Aucun compilateur, probe, import/calcul Python, builder ou nouveau banc n'a été invoqué pour cette révision.

## Dépendances et preuve conservée

RationalLogQuantization22 dépend de mathlib4.15 et ajoute explicitement Mathlib.Data.Rat.Cast.Order, qui importe Rat.Cast.CharZero. QuantizedLambdaEnvelope22 importe ce premier module local et mathlib ; sa source est une copie byte-identique526354f4… de l'ancien second module. Il ne doit pas être compilé avec le premier module9e59… ayant échoué ni avec un objet auteur présumé acquis. Aucune dépendance locale supplémentaire ni hypothèse de précision finale n'est introduite.

N=M=100000000, K=2^27, S=2^58 sont inchangés. Le vrai HasSum de log(1+z)−log(1−z), les termes positifs de queue et la série géométrique construisent R32=9/(4·65·3^65). Pour2≤p≤100000000, k=Nat.log2 p≤26 et z=(p−2^k)/(p+2^k)∈[0,1/3]. La boîte log32, nearest-even du milieu et le clamp[0,32S] produisent le point canonique A32(p). La precision≤1/S reste dérivée du constructeur avec ces seules gardes ; aucune boîte, epsilon, valeur finale de log ou majorant n'est une prémisse libre.

Le second module conserve les vraies branches IsPrimePow/minFac, toutes les PP, puis la borne Λ≤32 et les erreurs des produits/sommes. Sa conclusion proposée reste |C_N−I_N/S²|≤(N+1)(64/S+1/S²), N≤100000000. Le paramètre formel de continuité est s>0 ; la précision construite concerne le S fixé. La garde tau entière est conservée. Réalisation native, couverture complète du catalogue, equality A32 des records, mots/carries, NTT/CRT et coefficient numérique restent des dettes séparées.

## Échec réel précédent et réparation limitée

Le Juge batch16 a invoqué uniquement RationalLogQuantization22 revision02 : START17:41:49.695884UTC, FIN17:42:26.679776UTC, exit1, aucun olean. QuantizedLambdaEnvelope22 est NON_INVOQUÉ. Le vrai log45311354041cb407df0372b3f764bdb2bf90ea66b0a3100b1b072945510ef5c6 contient quatre erreurs d'élaboration. Ses38 impressions comportent28 listes standards non vides, une liste vide pour clampInteger et neuf sorryAx de recovery ; aucun résultat de ce module n'est crédité.

Ancienne ligne70 : le simplificateur ne déroulait pas logTerm partiellement appliqué au niveau du HasSum. La révision transporte le vrai HasSum par congr_fun, puis normalise chaque terme appliqué avec les casts Nat.add/mul/ofNat/one. Le coefficient est exactement celui de l'API primaire, pas une nouvelle série postulée.

Anciennes lignes151 et190 : exact_mod_cast ne transportait pas la borne Rat≤1/3 vers Real. Chacune utilise maintenant Rat.cast_le(K:=ℝ) pour une borne entre deux rationnels explicitement castés, puis Rat.cast_div/one/ofNat pour identifier le second membre réel. Aucun ordre n'est ajouté en prémisse.

Ancienne ligne236 : exact_mod_cast laissait le cast de la valeur absolue rationnelle. La nouvelle preuve transporte d'abord la vraie inégalité nearestEven_error via Rat.cast_le, puis paie explicitement Rat.cast_abs/sub/intCast/div/one/ofNat. Le point nearest-even reste inchangé.

APIs vérifiées dans les sources locales : Log/Deriv275–290 ; InfiniteSum/Basic52–75 (HasSum.congr_fun généré par to_additive depuis HasProd.congr_fun) ; Rat/Cast/Order10–102 et imports1–10 ; Rat/Cast/Defs65–160 ; Rat/Cast/CharZero25–110. Lectures TARGETED seulement, pas compilation ou fermeture des imports.

La comparaison statique d62ff6 confirme tous les en-têtes/domaines/defs/prints identiques et l'absence de sorry/admit/axiom déclaré/unsafe/native_decide. Elle n'est pas un parseur Lean ni un PASS. Les deux premières sources et les copies du lot16 restent immuables. Le total officiel reste76/1252 après observation ROOT ; aucune victoire, minoration de frontière, H1, D_N ou Goldbach n'est acquitté par cette révision.