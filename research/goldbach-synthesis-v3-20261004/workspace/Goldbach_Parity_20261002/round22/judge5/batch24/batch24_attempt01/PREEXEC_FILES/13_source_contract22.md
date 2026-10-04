# BORD — réparation SOURCE03 du vrai FAIL23

Statut : nouvelle source, non compilée. Ancienne source02 SHA3719a79cfd8aa0915cb15aa57111ac0529a3fa245387ceff19540395aa5756ea, copies Juge23, gate et sorties réelles conservées immuables. Aucun retry, compiler, APIprobe, interpréteur de candidat ou calcul numérique par l'auteur. Les trois réparations portent uniquement sur les sites effectivement diagnostiqués, sans modification d'énoncé, domaine, définition, nom ou ordre de déclaration. Catalogue manuel inchangé : **30 déclarations =22 théorèmes +8 définitions**,30 `#print axioms` qualifiés.

Le log réel `judge5/batch23/batch23_attempt01/AngularMellinBorder22.log`, SHAa9c287bf1dff63999fa115dd1e71e9b83d142883c62b89254b522e51002fc0a9, est lu FULL9aa9b9, avec le FIN réel. START21:37:14.356259UTC→FIN21:37:45.406858UTC, exit1, aucune olean,30prints dont19standards et11 `sorryAx` de récupération,5 avertissements de linter. Le module entier reçoit **zéro crédit**. Le log n'établit ni défaut mathématique ni obstruction de parité.

## Trois corrections statiques exactes

1. Ancienne ligne80 : après `hb.cexp.comp_ofReal`, le compilateur normalise le caractère en `exp(y*(I*−N))`, tandis que le but garde la fonction partiellement appliquée `angularCharacter N`. SOURCE03 fait d'abord un `change` explicite vers la lambda exponentielle complète, y compris la valeur dérivée, puis normalise les produits avec `mul_comm`, `mul_left_comm`, `mul_assoc`. La dérivée reste issue de la vraie composition, sans identité du caractère en prémisse.
2. Ancienne ligne116 : le but résiduel réel est `((-1)^N)⁻¹=(-1)^N`. SOURCE03 réécrit `← inv_pow` puis applique `norm_num` à l'inverse de−1. L'API `inv_pow` est lue TARGETED dans `Algebra/Group/Basic.lean409–426` (22702a) : elle donne `(a⁻¹)^n=(a^n)⁻¹`. Les valeurs exponentielles aux bords viennent toujours de `exp_nat_mul`, `exp_neg` et `exp_pi_mul_I`.
3. Ancienne ligne176 : `congrArg (fun z=>I*z)` conserve cette lambda dans l'égalité. SOURCE03 fait un `change` explicite dans h pour exposer les deux produits `I*(...)` avant `rw [he]`. Il ne pose aucune balance en prémisse : h vient toujours du théorème de balance dérivé via FTC.

Les avertissements de séquençage des tactiques ne sont pas élargis en une refonte. Aucun site sans diagnostic nouveau n'est retouché. La prochaine compilation indépendante peut encore révéler une erreur d'élaboration ; ce contrat ne lui attribue pas un PASS anticipé.

## Identité, branche et charges conservées

Pour a>0, q quelconque complexe, N naturel et N>0 dans la récurrence divisée,

\[
 J_{a,N}(q)=\frac1{2\pi}\int_{-\pi}^{\pi}(a-i\theta)^{-q}e^{-iN\theta}\,d\theta
 =\frac{i(-1)^N}{2\pi N}[(a-i\pi)^{-q}-(a+i\pi)^{-q}]
 +\frac qN J_{a,N}(q+1).
\]

La puissance est principale ; la partie réelle a>0 paie le slit-plane et l'absence de zéro pour chaque θ réel. Les dérivées complexes sont construites puis restreintes au réel. La continuité paie les deux `IntervalIntegrable ... volume` nécessaires ; FTC conserve les deux bords. Aucune intégrabilité ou dérivée finale n'est offerte en prémisse. Le caractère a les mêmes valeurs aux deux bords ; la puissance n'est jamais déclarée périodique.

Le bord vaut zéro pour q=0. Pour q=1, la conclusion concrète est `−(−1)^N/[N(a²+π²)]≠0`. Aucun bord non nul universel n'est prétendu. La normalisation n'emploie pas le symbole canonique α. Aucune dépendance locale, olean auteur ou hypothèse numérique n'est ajoutée. Les API de la source02 déjà lues restent readonly ; seule la signature d'inversion mentionnée ci-dessus est ajoutée aux lectures ciblées.

La formule complexe Mellin globale, la corrélation tronquée, les échanges spectraux, une nouvelle loi signée des phases, tous les termes PP/front/ledger, la cible D_N et WIN restent ouverts. Les anciens acquis et tous paquets natifs/Lean sont préservés. Le nouveau brouillon Mellin complexe22 est suspendu séparément, sans crédit ni compilation.
