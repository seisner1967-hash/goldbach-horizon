# Relecture indépendante du candidat ChenWeight

Source inspectée : `lean\ChenWeight.lean` de l'Agent 4, avant son passage au Juge. Relecture mathématique et de portée uniquement ; aucune modification de ce fichier, aucune compilation par ce relecteur.

## Identité locale

`factorCount n` est `ArithmeticFunction.cardFactors n`, donc la longueur de `n.primeFactorsList`, avec multiplicité. Le poids est

`W(n) = (Ω(n)−2)(Ω(n)−3)/2 = 3−2Ω(n)+Ω(n)(Ω(n)−1)/2`.

La preuve de Ω≤3 conserve chaque occurrence : si tout premier divisant n est >α, chaque entrée de la liste est ≥α+1 ; ainsi `(α+1)^Ω(n)≤n`. Sous `n≠0` et `n<(α+1)^4`, Ω≥4 est contradictoire. Sous `1<n`, Ω≥1. Pour Ω∈{1,2,3}, W vaut respectivement 1,0,0, et Ω=1 équivaut à la primalité. L'identité locale suit sans hypothèse carré-libre et sans estimation analytique.

Les puissances propres `p²` et `p³` ont Ω=2 et 3 et donnent correctement W=0. Cela aurait été faux avec le nombre de facteurs premiers DISTINCTS. Le terme `Ω(Ω−1)/2` compte des paires d'occurrences distinctes dans la liste ; les valeurs premières de ces occurrences peuvent être égales. Il ne doit pas être présenté comme une somme uniquement sur p<q. À facteurs entiers positifs a,b, l'additivité Ω(ab)=Ω(a)+Ω(b) permet une expansion bilinéaire, mais aucune petite norme analytique des coefficients ne suit de cette additivité.

Les cas n=0 et n=1 sont réellement exclus par `1<n` dans le détecteur, ce qui est nécessaire : leur Ω vaut zéro et leur poids vaut trois. Dans le lemme Ω≤3, n=0 est séparément exclu et n=1 est sans problème. Pour α=0, le domaine `1<n<(α+1)^4` est vide ; une hypothèse α≥1 n'est donc pas nécessaire. La variante `n<N≤α^4` est correctement plus restrictive et n'autorise aucun cas parasite.

## Coefficients et supports

`weighted_prime_identity_real` garde une somme finie et un coefficient réel arbitraire c(t). Il permet de retenir sans changement les logarithmes, fenêtres, unités modulo N, poids de Vaughan, détecteurs carrés-libres et masques déjà présents, en les incorporant dans c. Il ne prouve pas que leur moyenne signée est petite, et ne permet pas de retirer une restriction de support sans une autre preuve.

Le domaine requis est une rugosité COMPLETE de l'argument auquel W est appliqué : tous ses facteurs premiers doivent dépasser α. La seule frontière `r>α` du changement de diviseur complémentaire ne donne pas cette rugosité. Le cadre du ZIP impose `I_W(n)` sur la première coordonnée n=ab, et des masques sur m=kr ; il ne permet pas d'inférer automatiquement la rugosité complète de r ni de m.

Autre distinction essentielle : si le poids est appliqué au cofacteur r, son égalité détecte la primalité de r. Le complément original est m=k*r ; r premier n'implique pas m premier lorsque k>1. Le carré libre de m n'élimine pas cette différence : k et r peuvent être deux premiers distincts. Une insertion dans le terme réel `−μ(ar) log b μ(kr)^2 log r`, avec N=ab+kr, doit conserver ce sens exact. Pour détecter la primalité du complément m, l'identité doit être appliquée à m et ses hypothèses doivent être prouvées pour m lui-même.

Le coordinateur retient ici une variante de recherche QUART avec α=ceil(N^(1/4)), assurant N≤α^4 ; cette variante rend la coupure quartique mathématiquement disponible. Le profil en N^(1/8) conservé dans la monographie ne satisfait pas globalement N≤α^4 et ne reçoit donc pas le même transfert. Les acquis du profil en N^(1/8) ne sont ni modifiés ni contredits par cette observation de domaine. Même pour QUART, la coupure numérique n'apporte pas la rugosité manquante d'un cofacteur arbitraire.

## Conclusion de relecture

Les énoncés actuels ont des hypothèses suffisantes et une conclusion arithmétique pertinente : un détecteur polynomial exact sur le secteur entièrement rugueux à au plus trois occurrences premières. Aucun défaut mathématique de cet énoncé local n'a été identifié. La vérification des termes Lean et des axiomes appartient au Juge. La connexion au résidu D_N demande encore la preuve des hypothèses sur les supports d'origine puis une estimation signée du poids ; aucun de ces deux transferts n'est fourni par l'égalité finie. Ce candidat ne constitue pas à lui seul une victoire.
