# Addendum 17 — deux masques unitaires et leur prix exact

**FINAL — production terminée.** Le rapport `agent1_calibrated_typeii.md`, SHA `446c2d8fe21c86b05fbaf0e2864e7129da1b964287f31ff4287c0a19251103a9`, reste figé. Cet addendum précise son masque et donne également le raccord avec un masque contenant d=77. Aucune banque ni compilation n'est exécutée ; les identités de changement de référence ne constituent pas un gain de parité.

## 1. Provenance et conventions

Un contrôle en lecture seule des pièces figées donne, pour **la banque Type I précise de la boucle 16**, `U={b:gcd(b,N)=1}` dans FINAL 1, section 1. Son producteur `round16/typei_checks.py`, ligne 33, définit `unit=bytearray(gcd(b,s.N)==1 ...)` et la ligne 35 vérifie J=51948. Le masque du rapport 17 prolonge cette convention de cette banque ; il n'est pas annoncé comme le masque de toutes les références physiques antérieures.

Pour supprimer toute ambiguïté, garder désormais deux conventions, sur la **même** fenêtre I de la boucle 17 :

```text
U_h^0  = {b∈I : gcd(b,hN)=1},
U_h^77 = {b∈I : gcd(b,77hN)=1},
J_h^e  = #U_h^e,
B_h^e(b) = (A/J_h^e) 1_Uh^e(b), e=0,77 ; h=1,3,39,
z_h^e(b) = β(b)−B_h^e(b).
```

Le rapport figé utilise **e=0**. Les facteurs s et q des images canoniques sont distincts de 7 et 11, donc β est aussi supporté sur `U_39^77`. La même masse A est utilisée pour toutes les références. Si A=0, tous les B et z sont définis comme zéro ; sinon leurs dénominateurs sont positifs. Cette distinction est publiée dans le nouveau test.

La fenêtre 17 est différente de celle de la boucle 16. Ses J, ses densités et son prix L3 sont donc recalculés sur I. Les valeurs numériques 38, 2 et 36 du banc 16 ne sont pas transportées dans cette fenêtre.

## 2. Changement de référence sans perte de prix

Pour toute fonction linéaire finie F appliquée à un profil de b, définir

```text
E77_h[F] = F(B_h^77−B_h^0).
```

Alors, exactement,

```text
F(z_h^0) = F(z_h^77) + E77_h[F].               (U1)
```

Trois fonctions ont des poids distincts et restent distinctes :

- `F_θ(f)=Σ_b f(b) θ_N(N−77b)` pour le prix premier et Γ ;
- `F_II(f)=Σ_(v,w) ξ_v κ_w f((N−vw)/77)` pour le témoin bilinéaire ;
- `F_II,raw(f)=Σ_(v,w) ξ_v κ_w f((N−vw)/77) Λ_N(vw)` pour son raccord raw, avec properpowers.

E77 est enregistré pour chacune. Il n'est ni supprimé ni identifié à un prix calculé avec un autre poids. Les couples v,w peuvent compter plusieurs diviseurs du même j ; cette multiplicité appartient au témoin analytique et ne crée pas de nouvelles capacités physiques.

Poser, dans chaque convention,

```text
L3^e[F]  = F(B_3^e−B_1^e),
L13^e[F] = F(B_39^e−B_3^e).
```

Le télescopage donne les raccords complets

```text
L3^77[F]−L3^0[F]   = E77_3[F]−E77_1[F],
L13^77[F]−L13^0[F] = E77_39[F]−E77_3[F],       (U2)
F(z_1^0)=F(z_39^77)+L3^77[F]+L13^77[F]+E77_1[F].
```

Ainsi, conserver une référence physique incluant 77 ne dispense pas de payer son changement avec la référence du rapport 17. Le L3 acquis est une identité structurelle sous la convention utilisée ; U2 explique comment la transporter. Aucun modèle S(bN), principal acquis ou référence−S(N)N n'est remplacé par B_h^e.

## 3. Le mode Type II sous le masque 77

Les variables, coefficients et gardes du rapport figé restent inchangés : `V=ceil N^(1/8)`, v premier dans `(V,2V]` et unitaire avec 3003N, `ξ_v=χ13(v)`, `κ_w=χ13(w)`, `j=v w`, `|ξ_v|,|κ_w|≤1`, `s>2V` et `s≠13`. Le masque β et la réindexation AP de q modulo 13v ne changent pas. **B2 et son R_BV restent donc identiques.**

Ajouter les deux facteurs 7 et 11 multiplie par au plus quatre le nombre de termes d'inclusion-exclusion. Ils sont unitaires modulo 13 et modulo v ; ils ne modifient pas les moyennes locales du caractère ni la loi 1/v de la référence. Les frais de front B4 et B5 deviennent les majorants conservateurs

```text
|F_II(B_3^77)| ≤ 208 ρ_3^77 V sqrt(N),
F_II(B_39^77) = −χ13(N) A h_0/12 + R_front^77,
|R_front^77| ≤ 480 ρ_39^77 V sqrt(N).          (U3)
```

En particulier, les bilinéaires sous le masque 77 satisfont

```text
T_3^77  = −χ13(N) A h_V/12 + E_3^77,
|E_3^77| ≤ R_BV+4a+208ρ_3^77 V sqrt(N),
T_39^77 = −χ13(N) A(h_V−h_0)/12 + E_39^77,
|E_39^77| ≤ R_BV+4a+480ρ_39^77 V sqrt(N).      (U4)
```

Le comptage des unités conserve le facteur exact `φ(77)/77=60/77`. L'inclusion-exclusion sur rad(h·77·N) a au plus `16·2^ω(N)≤32sqrt(N)` termes pour h=39. Le principal unitaire de la longueur `|I|≥N/(8d)−1` domine ces fronts au source et donne la borne conservatrice

```text
J_h^77 ≥ N/[64d(1+u/log2)], h=3,39.           (U5)
```

C'est la variante de la borne 32 du rapport pour le masque sans 77. Après la **même** normalisation `λ=x/A`, on conserve

```text
|T_hat_39^77| ≤ x/(6V)+(x/A)(R_BV+4a)
               +480x V sqrt(N)/J_39^77.       (U6)
```

Le gain `h_V−h_0=Σ1/[v(v−1)]≤h_V/V` reste le même. La conséquence pour un B fixé conserve le **seuil BV supplémentaire inconnu** et ne contrôle qu'une paire de coefficients. Le prix E77 et les prix L3/L13 ne sont pas des économies additionnelles.

## 4. Complément obligatoire du contrat numérique

Le test neuf de la fenêtre `974026≤b≤1136363` publie les deux familles de masques `U_h^0` et `U_h^77`, pour h=1,3,39, avec leurs comptes J, densités exactes et facteurs exclus. Il vérifie U1/U2 pour les poids premier, Type II et Type II raw. Les prix `E77_h`, `L3^e`, `L13^e` sont conservés séparément ; aucune égalité entre les deux conventions n'est supposée.

Les endpoints AP de β restent ceux coupés réellement par `max(a,11s,11,ceil(b_min/s)−1)`, avec `H_s=floor(b_max/s)`. Les fronts candidats, les produits v=17 ou 19, les multiples de 323, les rawproperpowers et les prix définis sur les vrais supports restent explicites. Le test peut vérifier les deux versions U4 par une décomposition finie avec **erreurs exactes**, sans utiliser BV ou les signes asymptotiques au N=10^8.

**Décision :** le rapport principal reste valide pour la référence sans 77 qu'il définit. L'addendum ferme le changement éventuel vers une référence incluant 77, avec prix et frais conservés. Aucun estimateur de Γ agrégé ou de tous coefficients Type II n'est ajouté ; aucune victoire n'est déclarée.
