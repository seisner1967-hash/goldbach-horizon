# ROLE3 H1 ψ — paquet SOURCE uniquement, boucle 22 / nœud 15.3

Les quatre modules contiennent 46 théorèmes et 8 définitions, avec 54 commandes
`#print axioms` qualifiées. Aucun compilateur, probe ou calcul Python n'a été
exécuté pour ce paquet. Une revue papier/API indépendante ROLE4 a lu les quatre
sources complètes (a84072/41e749) et ne signale pas de trou analytique ; cette revue ne constitue
pas un PASS Lean. La compilation reste fermée après l'échec technique d'export
du premier nouveau banc composants : aucun résultat numérique PASS n'est lié.

L'ordre futur est Core → BetaLimit → Integral → Duplication, une seule invocation
par module, arrêt au premier code non nul, dépassement du délai, olean absent,
audit d'axiomes incomplet ou axiome extérieur à propext/Classical.choice/Quot.sound.
Les copies `source_final/` et leurs SHA seront les sources effectives. Les
modules précédents seront importés exclusivement depuis la sortie neuve.
ΓPrerequisites22 Juge batch02 est disponible en lecture seule ; les quatre
modules ψ n'en ont aucun import direct et aucun ΓContourComponent ancien
n'est importé. Les huit bibliothèques du cache et le runtime Lean 4.15 restent
les dépendances de compilation. Leur fermeture d'importations sera calculée
par lecture des lignes `import`, distinguée d'une lecture mathématique FULL.

Le launcher SOURCE exige un manifeste final lié au vrai reçu numérique exit1
2c740908…/intégrité, sans PASS ni contre-exemple mathématique établi, les
runtimes exacts et une gate ROOT distincte. ROOT a précisé que cet échec
TECHNIQUE_EXPORT ne doit pas devenir une précondition mathématique artificielle
pour P1 : la gate peut autoriser la compilation auxiliaire sans nouveau PASS
numérique, en conservant explicitement cette observation. Il capture les inputs avant START, garde commande,
START/FIN, logs, prints, olean et POSTEXEC, sans retry. Le manifeste présent
est PREPARED_SOURCE_ONLY avec noNumericPASS. La gate reste requise ; aucun
lancement n'est implicite dans ce statut. Une réfutation numérique véritable
tuerait l'itération, contrairement à l'échec d'export documenté.

## Charge analytique réellement rédigée

`gammaPsi z` est `deriv Complex.Gamma z / Complex.Gamma z`. Core paie la
récurrence et ψ(1)=−γ à partir des vraies dérivées de Γ. Pour Re z>0, le
quotient R_z(w)=Γ(z)Γ(w+1)/Γ(z+w) vérifie R_z(0)=1 et R'_z(0)=−γ−ψ(z).
Pour w réel positif, R_z(w)=w B(z,w) et B(1,w)=1/w. La limite de sécantes
le long w_n=1/(n+1) est donc la limite réelle des différences bêta.

BetaLimit garde leur intégrande entier :

    [(t^(z−1)−1)(1−t)^(w−1)].

Pour w≥0 et 0<t≤1, sa norme est dominée par la fonction effectivement définie

    M_z(t)=2(t^(Re z−1)+1)+‖z−1‖[1+(1/2)^(Re z−2)].

Sur la moitié gauche, (1−t)^(w−1)≤2. Sur la moitié droite, la vraie dérivée
de t^(z−1) et MeanValue donnent l'annulation ‖t^(z−1)−1‖≤C_z(1−t), puis
(1−t)^w≤1. Le point t=1 est traité séparément avec numérateur nul.
L'intégrabilité de M découle de Re z−1>−1 ; les différences bêta positives
fournissent la mesurabilité. La limite AE paie celle de l'intégrande final.
DCT puis unicité de la limite donnent ψ(z)=−γ+∫0..1(1−t^(z−1))/(1−t)dt.

Integral prouve l'image de exp(−u), son injectivité, sa dérivée négative et le
Jacobian absolu. Les deux théorèmes Jacobian transportent l'intégrale ET son
intégrabilité depuis le résultat Beta. La cible P1 n'a que Re z>0 en prémisse :

    ψ(z)=−γ+∫_(u>0)[exp(−u)−exp(−zu)]/[1−exp(−u)]du.

Duplication différentie la vraie identité de Legendre, avec les facteurs Γ,
la puissance de 2 et √π tous non nuls, puis divise les deux expressions.
Aucune P1, série digamma, convergence, majorant ou identité χ n'est admis.

## Première dette suivante, explicitement ouverte

P1 attend encore la vraie compilation auteur puis le Juge indépendant. Même
un PASS de ces quatre modules ne fermerait pas C5. Il faut construire la
réécriture exacte du vrai χ′/χ, puis l'intégrabilité du noyau mixte avant Fubini,
les substitutions u=2v et x=exp(v), et le raccord au Arch fixé :

    Iχ=(log(4π)+γ) f_Y(1)+Arch_Y−1,
    Arch_Y=∫_(x>1)[f_Y(x)+f_Y(1/x)/x−2f_Y(1)/x]/(x−1/x)dx.

Le −1 provient des deux intégrales complémentaires de f_Y(x)/x, dont la somme
vaut 1. Il ne peut être supprimé ou absorbé dans une nouvelle définition Arch.
Une borne papier concrète pour le futur Fubini est conservée dans le document
`C5_next_obligations22.md`, sans statut de preuve Lean ni prémisse libre.
Le global H1, le coefficient N, le ledger D_N et la victoire restent ouverts.
