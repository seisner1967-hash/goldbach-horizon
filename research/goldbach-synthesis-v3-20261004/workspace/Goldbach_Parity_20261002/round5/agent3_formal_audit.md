# Agent 3 — boucle 5 : coordonnées entières de déterminant

Nouveau module autonome : `round5\lean\DeterminantCoordinates.lean`, imports mathlib seulement. Aucun fichier d'un acquis, d'un ancien constructeur ou d'un reçu n'a été modifié. Le filtre central `round5\hecke.json`, statut PASS, et `round5\conservation.json`, statut PRESERVED, ont été LUS avant la première compilation ; la notification de l'Agent 6 avait également été reçue avant le lancement.

## Cœur HNF formalisé

Les variables générales sont des entiers. Sous N>0, uB+sD=N et les deux divisibilités `N | u+λD`, `N | s−λB`, les quotients A=(u+λD)/N et C=(s−λB)/N satisfont

`NA−λD=u`, `NC+λB=s`, `AB+CD=1`.

La preuve des deux reconstructions utilise la division euclidienne EXACTE et les témoins de divisibilité. La preuve AB+CD=1 annule le produit N·(AB+CD−1)=0 au moyen de N≠0 ; elle ne procède pas à une division dans les rationnels. Le module prouve ensuite les quatre entrées de `Hλ*G=M` dans `Matrix (Fin 2) (Fin 2) ℤ` et `det G=1`.

Le sens inverse prend AB+CD=1 et pose u=NA−λD, s=NC+λB. Il donne uB+sD=N et les deux divisibilités. Sous N≠0, les quotients ainsi reconstruits récupèrent EXACTEMENT A et C. Les deux sens n'utilisent aucune hypothèse de petitesse, de primalité ou de distribution.

## Existence canonique de λ effectivement obtenue

Ce module ne se limite pas à supposer les congruences. Le théorème `exists_canonical_lambda_of_coprime` les produit à partir de

`N>0`, `uB+sD=N`, `Int.gcd N B=1`.

Bézout fournit η,ζ avec Bη+Nζ=1. Prendre λ₀=sη donne N|s−λ₀B. L'égalité du déterminant donne N|B(u+λ₀D), puis la vraie coprimalité permet d'annuler B. Enfin λ=λ₀ mod N appartient à [0,N) et les témoins de divisibilité sont ajustés par le quotient λ₀/N. Toutes ces opérations sont démontrées dans les entiers de Lean.

La coprimalité B,N reste une hypothèse de ce théorème : le module n'ajoute pas son transfert depuis le masque original `gcd(n,N)=1`. Ce transfert est élémentaire par B|n dans le cadre réel, mais il ne doit pas être présenté comme déjà inclus dans la déclaration. L'unicité de λ et sa propre unité modulo N ne sont pas formalisées ; cette dernière demanderait aussi l'unité de s modulo N. La preuve d'existence et les deux congruences, elles, sont intégralement formalisées.

## Divisibilités des tuples conservées

`tuple_quotient_reconstruction` garde explicitement b*x|B et k*z|D, puis prouve

`b*(B/(b*x))*x=B`, `k*(D/(k*z))*z=D`.

Le sens inverse prouve que B=b*v*x et D=k*t*z redonnent v,t par leurs quotients lorsque b,k,x,z sont positifs. Il n'affirme pas qu'une matrice arbitraire représente un tuple admissible. Les seuils y, la rugosité, les caps, les faces, les fenêtres, les logarithmes et le module CRT ne sont pas déclarés invariants sous ces coordonnées. Aucune égalité de poids agrégé complet n'est ajoutée.

## Shear et véritables valeurs de Möbius

Le shear `T(j)=[[1,j],[0,1]]` a déterminant un et envoie

`[[u,s],[-D,B]]` sur `[[u,s+j*u],[-D,B−j*D]]`.

Le module certifie les deux factorisations entières avec le MÊME λ=73626461 et le shear j=−78 :

`Hλ * [[9260,−67],[−12577,91]] = [[3,7951],[−12577,91]]`,

`M*T(−78) = [[3,7717],[−12577,981097]]`,

`Hλ * [[9260,−722347],[−12577,981097]] = [[3,7717],[−12577,981097]]`.

Les deux bases G ont déterminant un et λ est dans [0,N). Les deux niveaux uB+sD valent exactement 100000000. Les quotients A,C des exemples et la divisibilité 13|981097 avec quotient 75469 sont certifiés.

La définition `expandedTupleSign(u,v,s,t)` est le produit des QUATRE vraies valeurs de μ, et pas une variable de signe choisie. `norm_num` prouve les primalités 3,7,7951,12577,7717,163,463. La multiplicativité et 75469=163·463 donnent μ(75469)=1. Lean conclut

`expandedTupleSign(3,7,7951,12577)=+1`,
`expandedTupleSign(3,75469,7717,12577)=−1`.

Ce changement porte sur le coefficient d'un TUPLE DÉVELOPPÉ. Il ne doit pas être confondu avec H₂(a)H₂(r), coefficient après agrégation des factorisations. Dans le banc exact, ce dernier passe de 4 à 0 ; cette valeur agrégée n'est pas un théorème de ce module. Le changement du signe développé dans une même représentation canonique refuse l'invariance automatique du coefficient par classe ; il ne réfute pas une annulation pondérée des bases.

Les masques de base des exemples ont été validés par le filtre numérique exact. Leur reproduction exhaustive comme propositions Lean, l'égalité abstraite des réseaux de colonnes, la bijection finie de tous les supports et les sommes pondérées sur ces réseaux ne sont pas formalisées ici. Les égalités matricielles, leurs bases de déterminant un, les quotients et les vrais signes le sont.

## Compilation et limites

`agent3_compile01.log` : une erreur technique de simplification conservait 0−D dans l'entrée basse gauche de HλG. Un avertissement signalait aussi une séquence de tactiques trop générale. Réparation par `zero_sub` et simplification directe. Aucun argument mathématique de HNF n'a échoué.

`agent3_compile02.log` : compilation complète, avec une suggestion informative `ring_nf` sur le shear. `agent3_compile03.log` : 14 théorèmes, aucune erreur ni avertissement, après remplacement de cette étape par la simplification des entrées. `agent3_compile04.log` ajoute le certificat concret des bases canoniques, de leurs deux déterminants et de leurs niveaux : version finale à 15 théorèmes, chacun muni de `#print axioms`.

Ce module constitue une représentation exacte standard, classée PARTIAL. Il n'apporte aucune norme contrôlée d'observable automorphe, estimation de Hecke, norme de Möbius ou gain dans le cumul signé. Le niveau N de la matrice ne remplace pas le module CRT ar des tuples. La cible D_N≤N/(256 log N log log N) reste non démontrée ; aucune victoire n'est revendiquée.
