# Retour statique20 sur PrimeHarmonic08–11

Lectures achevées le 2026-10-03 03:27:27 UTC : FULL des quatre sources PREEXEC, logs et START08/09/10/11 ; registre auteur décodé puis entrées08–11 extraites. Les rapports01/02 demeurent inchangés. Aucune compilation, aucun calcul mathématique, aucune modification des sources/FINALs/gates, aucun nouveau nœud. Le présent rapport ne juge aucune tentative12 ou ultérieure.

**08–10 échouent sur des détails de formalisation. 11 corrige ces détails en gardant les mêmes énoncés et gardes, puis compile dans l’exécution auteur stockée. Aucun des FAIL examinés ne réfute l’Euler ou Rankin et aucun ne constitue un obstacle de parité.**

| Tentative | START → FIN, UTC | Exit | Diagnostic réellement observé |
|---|---|---:|---|
|08|03:19:56.238447 →03:20:37.189202|1|Deux cas N=0 ouverts, mauvais nom/qualification du lemme intégral, identifiant inverse inconnu, tactiques après clôture du but.|
|09|03:21:29.356324 →03:22:09.389282|1|L’import de l’intégrale ne corrige pas encore la qualification `intervalIntegral.integral_rpow`.|
|10|03:22:29.639682 →03:23:13.771787|1|Reste l’égalité algébrique `N^(-σ)−1 = −1+N^(-σ)` après l’application du lemme.|
|11|03:23:39.322979 →03:24:22.923843|0|Ces buts sont fermés ; quatre warnings de séquençage, impressions d’axiomes usuels sans `sorryAx`.|

## Cause et correction

- [Log08](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt08.log:1) laisse, dans les deux branches N=0, `0≤1+σ⁻¹`, malgré `hs:0<σ`. [PREEXEC09](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt09_source_PREEXEC.lean.txt:15) ajoute `positivity` après la simplification. La positivité de l’inverse est une conséquence de la garde existante ; aucune hypothèse analytique supplémentaire n’est ajoutée.
- Les logs08/09 signalent une notation de champ invalide pour `intervalIntegral.integral_rpow`, puis l’échec de `rw`. La correction conserve l’intégrande x^(-1−σ), l’intervalle [1,N], la garde σ>0 et les obligations de l’intégrale. Après l’import `Mathlib.Analysis.SpecialFunctions.Integrals`, [PREEXEC10](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt10_source_PREEXEC.lean.txt:37) utilise `integral_rpow`. L’erreur concerne l’accès au lemme dans le cache mathlib fixé, pas l’existence de l’intégrale papier.
- Log08 rapporte `unknown identifier 'inv_le_iff₀'`. La réparation09 utilise `inv_le_iff_one_le_mul₀`, avec les mêmes gardes de positivité de 1−t et logY. Elle retire aussi les tactiques superflues après les buts déjà résolus. Un `no goals to be solved` est un incident de script, pas un manque de preuve mathématique.
- [Log10](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt10.log:1) isole le dernier reste : la commutativité de l’addition dans `N^(-σ)−1 = −1+N^(-σ)`. [PREEXEC11](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt11_source_PREEXEC.lean.txt:38) complète la normalisation par `ring`. Ce passage ne change ni la constante 1+σ⁻¹ ni un domaine de sommation.

Les `sorryAx` des tentatives échouées proviennent des objectifs non fermés et se propagent vers les théorèmes qui les utilisent. [Log11](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt11.log:1) les élimine dans toutes ses impressions ; le registre11 indique exit0 et l’olean `dababb47d7453bcef79e4a71e6486f042fcab96cd272126c51cf1612c63ba36a`. Ce constat repose sur les artefacts auteur stockés, sans réexécution et sans substitution au Juge indépendant.

## Portée exacte du PASS11

La chaîne fournit la p-série à l’exposant −1−σ, σ>0, puis Eminus≤1+σ⁻¹ et le majorant harmonique des premiers. La sommabilité globale est utilisée pour cette p-série convergente ; Eplus à σ−1 conserve la vraie sommabilité sur les entiers friables au support fini de premiers acquise dans EulerRankin05.

[actual_euler_plus_le_u_pow_27](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt11_source_PREEXEC.lean.txt:200) conclut Eplus≤u^27 à partir de u>0, logY≥4 et 1+logY≤u. [La masse de B_D](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt11_source_PREEXEC.lean.txt:242) reçoit u^−37 avec, en plus, D>0, logD≥u/2 et `128 logu logY≤u`. [Le tail tau](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/role4/attempt11_source_PREEXEC.lean.txt:279) reçoit N·u^−42 avec M>0 et logM≥3u/4 à la place de la garde sur D. La petite masse et le poids tau réel sont des conclusions dérivées, pas des champs libres. Le majorant prime-harmonique D9 de la prospective n’est pas une prémisse ajoutée ici.

Le raccord de ces gardes aux vrais floors/ceils source demeure nécessaire. 11 ne fixe pas Y=floor(exp(u/(128logu))), D=ceil(sqrt N), M=ceil(N^(3/4)), ne prouve pas D≤M ou E≤a depuis ces paramètres et ne conclut ni F2 ni F4. Les limites F3 local/F0 privé de F1/support source/ledger exposées dans [rapport02](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round20/ideation_failure_feedback02.md) restent distinctes. Les variantes plus fortes de la prospective ne reçoivent aucun crédit. Les deux mécanismes d’idéation restent inchangés ; une victoire locale n’est pas annoncée.

## Entrées SHA256 et provenance

Chemins sous `Goldbach_Parity_20261002`. Hashes observés et comparés aux STARTs/entrées du registre ; aucun ancien producteur ou PASS n’est réexécuté. Le fichier courant PrimeHarmonic a le même hash que PREEXEC11.

| Entrée | SHA256 |
|---|---|
|round20/role4/attempt08.log|8c5544fbd9801e9e991e1da7addd5f7c3349a11a61f78646b718c46b4b60016d|
|round20/role4/attempt08_source_PREEXEC.lean.txt|afcda87bb299e254f5680e5f95297144c61a8218b92f34309f6f390ddfdea224|
|round20/role4/attempt08_started.json|3aeb7d44f61b228b16a3be2214c43169a488e13096bc4b6655a188d3dcc3d810|
|round20/role4/attempt09.log|92618ef68daae81ed61df8b4a24c6f0eaf7d6fd34538a464abda2dae7a135484|
|round20/role4/attempt09_source_PREEXEC.lean.txt|8e17e843475a75fd1667cb2aba8feafe6b0fbff4c126620f66c214bb2b555815|
|round20/role4/attempt09_started.json|93e0b393a6b5d1d6b6973c7c01b27d88c9c85b926f4077ede7d5b3a83ab8e3d1|
|round20/role4/attempt10.log|61778e8bd0a5bd4130645d392694469633983a66cb39f097157bc1adb686a006|
|round20/role4/attempt10_source_PREEXEC.lean.txt|7bc01aca55b63a4aa18f3c18d4d6e05fc9daf170cb951911f3e76c7933933b18|
|round20/role4/attempt10_started.json|17b09d5a8b796d62a2f0bf0dd60e29ff8df5d201f5d5b16e4e74548d8227dc61|
|round20/role4/attempt11.log|7e115ec91abe28ed51dffa89035c23f6db1c197b5264635a412addad5bef32ab|
|round20/role4/attempt11_source_PREEXEC.lean.txt|53df26ec4a5880427d81ab394855f3d89238485487a07c6e36086b576f2894d4|
|round20/role4/attempt11_started.json|7b8e8fb8585b3a50dfc11ed805392f9eff68b7850154a57689e538c9b5250d04|
|round20/ideation_failure_feedback01.md, inchangé|562783b7999486ee57fcb66743c08cd52017c3694bca75a45c61198ec9be7d5f|
|round20/ideation_failure_feedback02.md, inchangé|6063a7f05091c3b2ae641d9a984aaa27194aa0b9dc765ca44aaf66e79a5f852b|

FULL logs08/09/10/11 : `18bbba`/`7138ca`/`ff89f4`/`47890c`. FULL sources08/09/10/11 : `0b2bf1`/`e35ea7`/`e1f864`/`246794`. FULL START08/09/10/11 : `d66b29`/`3d627c`/`709642`/`6e2199`. Registre08–11 extrait : `ae8305`. Hashes : `11f11e` ; repères de lignes : `954306`. Le hash intermédiaire de PrimeHarmonic relevé dans le rapport02 correspond désormais au PREEXEC10 réel ; le rapport02 conserve sa qualification d’observation statique.
