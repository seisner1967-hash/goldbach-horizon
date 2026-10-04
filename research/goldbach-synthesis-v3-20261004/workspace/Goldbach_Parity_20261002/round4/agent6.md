# Agent 6 — boucle 4

Les deux bancs ont terminé avec **code 0 et PASS**. Les calculs emploient des entiers ou `Fraction`. Les fichiers antérieurs restent en lecture seule.

## Chart affine réel à N = 10^8

`affine_checks.py` vérifie **12 400 intersections rationnelles**, exhaustives pour les six coefficients dans {-2,-1,0,1,2} avec déterminant non nul. La résolution exacte annule simultanément une forme de chaque branche ; les deux produits HH s'annulent au point obtenu.

Le chart entier `u=3+7951X`, `t=12577-91X`, avec b=13,v=7,w=k=z=1,s=7951, vérifie l'identité polynomiale `91u+7951t=100000000`. Son rang est 1. Les 303 points X=0,...,100 et Y=-3,0,5 sont positifs ; **25 faces X distinctes** respectent aussi les sélecteurs d'unité, de carré-liberté, le core et W=2. Le témoin original X=0 est conservé.

Sans non-dégénérescence, `13*X*Y*0+N=N` donne un chart de rang 2. Sans N≠0, `X*Y-X*Y=0` a rang 2 et deux produits non nuls en (1,1). Une identité vérifiée seulement sur quelques points positifs ne remplace pas l'identité polynomiale : la variation indépendante u:3→11,v:7→17 donne une différence mixte **1040**. Ce filtre ne s'étend pas aux charts non linéaires.

## Inverse-completion et reste non unité

`inverse_checks.py` représente chaque somme exponentielle par ses coefficients entiers de phases et réduit le polynôme modulo **Φq construit exactement par divisions moniques de X^q-1**. Aucune approximation complexe ou flottante n'intervient.

L'identité `τH=qFχ-E_nonunit` et sa version à deux axes passent sur q=11,15,100, pour F=G=δ1 puis pour deux supports signés complets. Sur q=15 avec caractère induit modulo 3, τH=3 et E=12 : supprimer le reste donne une projection **1/25** au lieu de 1. Sur q=100, caractère induit modulo 5, τ=0 et E=100.

Au vrai **N=10^8=2^8*5^8**, les unités sont exactement les quatre classes modulo 10. La translation de N/5 conserve ces classes et le caractère modulo 5 ; chaque orbite de longueur 5 s'annule par `1+ζ5+...+ζ5^4=0`. Ce certificat couvre les 40 millions d'unités structurellement, sans les énumérer. L'identité exacte exige alors le reste entier E=N pour F=δ1.

Le benchmark cyclique q=100,R=70,K=3 conserve **C=s*t et tous les h,l**. Pour C=33 et eta=3, le support réel donne 1 ; figer le support C=21 donne 2. Les identités de collision, avec diagonales retenues, donnent les énergies exactes **6 et 2**. Ces petits benchmarks ne sont pas présentés comme les fenêtres HH originales ni comme une estimation asymptotique des six moments.

Restreindre h,l aux seules unités donne **1/10 au lieu de 0** pour C=21, et **2/5 au lieu de 1** pour C=33. Le complément non unité ne peut donc pas être supprimé dans cette identité.

Les scans et identités n'apportent **aucune borne globale sur D_N**.

## Provenance

- `affine_checks.py` : `c9eecbd240600743b463e2eebba83988a5a0e5c5a40ee8051f368cd1c132725e`.
- `inverse_checks.py` : `4a9e78c5e9e3003bb0a3b12507a8fcf65924e1eb12d21ababa363c88f0190a4c`.
- `affine.json` : `dcffa8ad5dd69e980fbc93e1adb474c0eb7aec8ddf558840e39f6c6394ec2feb`.
- `inverse.json` : `5730cccbd23e5f8326a1f8258281ca1d74c6123624e8bacc03e3a26bf4c37783`.
- Domaines et données complètes : `affine.json`, `inverse.json`.
- Sorties conservées : `affine_run.log`, `inverse_run.log`.
