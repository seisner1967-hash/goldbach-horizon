# Q394 / RS22H

## Verdict

**Brackets historiques 414 et 415 : fermes. Bridge A : OPEN.**

Chaque bracket annonce possede deux signes stricts certifies et un theoreme
d'existence d'un vrai zero de `riemannZeta` strictement entre ses rationnels.
Ni unicite, ni simplicite, ni compte global exact ne sont deduits du seul
changement de signe. La sous-famille exacte a 2 element(s),
indices Lean [413, 414]; sa numerotation historique est [414, 415].

## Cible prioritaire

```lean
Q394Probe.bracket415_zeta_zero :
  exists t : Real,
    (Q394Probe.lo415 : Real) < t /\ t < (Q394Probe.hi415 : Real) /\
      riemannZeta (Q343Probe.criticalPoint t) = 0
```

Les bornes exactes sont `3007751592067/4294967296` et
`751937898017/1073741824`. La borne droite positive est celle de Q393.
Q394 reconstruit independamment les huit atomes gauches, leur replay,
la decomposition et le reste; la proximite des endpoints ne transporte aucune preuve.

## Second bracket ferme

`Q394Probe.bracket414_zeta_zero` porte exactement sur
`lo414 = 3002749485653/4294967296` et
`hi414 = 1501374742827/2147483648`. Les huit atomes de chacun de ces deux
points sont reconstruits et certifies independamment. Les signes Hardy sont
respectivement positif et negatif. `brackets414415_distinct_zeta_zeros`
prouve simultanement deux vrais zeros, avec `t414 < t415`.

La famille historique compte donc deux lignes closes sur 649; les signes des
647 autres lignes ne sont pas annonces comme acquis.


## Methode et controle

- Ordre 63, index 10, huit valeurs reelles de `2 * Re(G * (S + A * B))`.
- 190 jets normalises de numerateur/denominateur/quotient pour chaque nouveau coefficient.
- Intervalles entiers signes sur grille `10^310`, avec arrondis exterieurs exacts.
- Seules les constantes independantes du point et les noyaux generiques sont reutilises.
- Rayon `1/400000000000000000000000000000`, avec nouvelle preuve ponctuelle et
  preuve uniforme sur tout l'intervalle reel `[699,7003/10]`.
- 860 nouveaux modules de production recompiles; 860 rejoues
  isolement, 860 artefacts byte-identiques.
- 2373 sources historiques locales importees;
  aucune recompilation globale n'est revendiquee. Treize dependances manquantes
  ont fait l'objet d'une restauration ciblee sans modification des sources.
- Types exacts et constantes des termes audites; axiomes `propext`,
  `Classical.choice`, `Quot.sound`; scan brut de production vide.

Les donnees numeriques exactes figurent dans `Q394_STATUS.json` et les fichiers
`*replay_candidates.json`; les candidats ne deviennent des certificats que via
les theoremes de membership effectivement compiles. Les rapports specialises
et journaux conservent les precisions et les methodes de generation.

L'extension separee `Q394RangeExtended` prouve un rayon `5e-30` sur tout
`[685,7003/10]`. Son checker et la couverture des onze intervalles historiques
405 a 415 sont compiles. Les neuf lignes 405 a 413 n'ont pas leurs signes
certifies par cette seule borne analytique. Le rayon plus serre `2.5e-30`
reste celui effectivement consomme par les nouveaux endpoints 414/415.


## Contrats historiques

La geometrie des 649 lignes est prouvee. Une famille complete requiert encore
les signes manquants. Le constructeur historique n'est pas affaibli; aucune
valeur par defaut ne remplace un bracket absent.

La sous-famille exacte `{413,414}` fournit une borne de multiplicite au moins 2.
Un consommateur distinct ajoute l'intervalle large `(14,15)` deja prouve en
Q358 et obtient une borne au moins 3. Ce troisieme intervalle ne remplace pas
le premier bracket serialise, et ces bornes inferieures ne sont pas des comptes exacts.


La largeur minimale d'une inflation symetrique de rayon `2.5e-30` est `5e-30`.
Le theoreme general `symmetricOutput_cannot_refine_historical` exclut donc le
raffinement universel vers la boite droite historique de largeur `1572/10^80`
avec cette strategie. Il ne nie pas l'appartenance mathematique a cette boite.

`FirstBracketAnalyticLeaves`, la famille semantique complete, les deux bornes
de Turing, le compte global et la saturation restent ouverts. Les signes du
carrier sont ponctuels; aucune boite numerique Hardy n'est reutilisee comme
boite du carrier. `TS340_UNCONDITIONAL` reste `OPEN_FROZEN`.

`Q394_CONTRACT_MAP.md` donne les types exacts des obligations restantes.
Le consommateur optionnel qui utilise `(14,15)` reste distinct des brackets
historiques exacts : il n'habite pas le premier intervalle serialise.

## Conservation et reproduction

HEAD et origin/main restent `433e29e`. Les 44 lignes preexistantes de
`lakefile.lean` sont preservees; le worktree n'est pas presente comme vierge.
Les archives Q391-Q393 ne sont pas reecrites. Le manifeste Q391 garde son
exception documentaire anterieure sur lakefile; elle n'est pas effacee.

La reproduction initiale des coefficients compare 194 sources apres normalisation
CRLF/LF, dont 193 identiques octet pour octet. Une difference de fins de ligne
est documentee; elle ne doit pas etre confondue avec la comparaison des `.olean`.
Les scripts et donnees necessaires sont inclus, avec les pins des dependances.

Gel des preuves : `2026-09-09T00:35:33.806310+00:00`. Echeance : `2026-09-09T01:36:10Z`.
La fin du packaging et son respect de l'echeance sont mesures dans l'attestation
exterieure au ZIP, avec ses SHA-256 et son extraction fraiche controlee.
