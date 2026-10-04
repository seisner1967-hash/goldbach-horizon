# Agent 6 — boucle 5

Les deux filtres centraux ont terminé avec **code 0, PASS**. Les formalistes 3 et 4 ont reçu séparément leur gate avant compilation. Tous les calculs sont entiers, rationnels ou des réductions cyclotomiques exactes.

## Conservation

`previous_artifacts_sha256.json` fixe **120 sources, scripts, reçus et builders antérieurs**. Les deux bancs les ont comparés après exécution : aucun changement. Le rapport central vivant, l'état du contrôleur et les caches de dépendances sont exclus explicitement. `conservation.json` résume cette vérification. SHA256 du registre : `b2a48fef1f5eccbc30ed516a0f5e20bd20042cb559aa997ac2d38602ddc32558`.

## HNF/Hecke au vrai N=10^8

`hecke_checks.py` vérifie M=HλG, les deux quotients entiers, det G=1 et AB+CD=1. Pour le témoin original, λ=73626461 et G=[[9260,-67],[-12577,91]].

La descente automatique du poids signé à cette classe est **fausse** : le shear j=-78 conserve les facteurs positifs, la classe, les masques d'unité et de carré-liberté, W=2, le core et les caps. Il remplace v=7 par v=75469=163*463 et s=7951 par s=7717 premier. Le produit réel μ(u)μ(v)μ(s)μ(t) passe de **+1 à -1**. Le poids signé log13*logr et le coefficient complet H2(a)H2(r), passant de **4 à 0**, ne sont donc pas constants sur la classe. Le module CRT original a*r reste explicitement dans les données et varie.

Sur les **204 shears positifs** j=-13ℓ, ℓ=0,...,203, **43** respectent tous les masques (24 signes positifs, 19 négatifs). Les shears -26 et -52 sont enregistrés comme sorties respectives de carré-liberté et d'unité. Ce test ne réfute aucune future compensation pondérée sur une classe entière.

## Fréquences et deux Gauss distincts

`frequency_checks.py` contrôle **89 988 égalités rationnelles échantillonnées** hx/N=ax/q' sur les **81 strates q' divisant N**, avec h=(N/q')a et gcd(a,q')=1. La partition de cardinalité N est certifiée structurellement par la somme exacte des φ(q'). Les fréquences au-delà du domaine déclaré ne sont pas présentées comme énumérées.

Pour χ induit du caractère quadratique modulo 5 à N=10^8, les orbites x=r+10j annulent gχ(h) sauf h multiple de N/10. Le petit calcul cyclotomique restant certifie **8 fréquences actives**, dans q'=5 et 10. Chaque strate contribue **50 000 000** à F=δ1 ; le reste non unité total est N. Cette preuve structurelle n'énumère pas 40 millions d'unités.

Les caractères **d'ordre 4 modulo 5 et 10**, codés par phases modulo 20, vérifient les conventions exactes :

    H = χ^{-1}(-1) τ(χ) Fbarχ,
    κ = χ^{-1}(-1) τ(χ^{-1}) τ(χ) = normSq τ(χ) = 5,
    E = (N-κ) Fbarχ sur support unités.

Les deux Gauss sont effectivement distincts. Les confondre est falsifié ; supprimer le support unités est aussi falsifié par F=δ2 modulo 10. Fbarχ peut être complexe et n'est jamais supposé positif. La double projection est vérifiée avec ses normalisations.

Les petits modules 15,100,385 sont des diagnostics séparés avec énumération complète. Le benchmark **N=70630, h=2, q'=35315**, caractère de conducteur 5, certifie une contribution non nulle : petit conducteur ne signifie pas petit module réduit en général.

**Aucune estimation asymptotique des moments ni borne sur D_N n'est déduite de ces contrôles.**

## SHA256 des scripts

- `hecke_checks.py` : `ba92c852c542adab1acbcd82d8021091099de99062ba5166ad49fe5f8f463fa5`.
- `frequency_checks.py` : `b841dab845ff60c94461345b34c66cec6983a8d25c205aec064d58d748c67601`.
- `hecke.json` : `e67b46ab0405408b1b295815fb88172579ec15fe22acaf5437e613552fbe8bed`.
- `frequency.json` : `e3048b49b8d175db4528046b17cb2e6769cd6368b1323e0587d54f70c5922d36`.

Les reçus complets sont `hecke.json`, `frequency.json` ; les sorties sont conservées dans `hecke_run.log` et `frequency_run.log`.
