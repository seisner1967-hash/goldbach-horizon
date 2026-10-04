# Juge batch04 — Core, BetaLimit, Integral

SOURCE seulement, gate fermée. Trois sources auteurs réellement PASS, copies
exactes : Core19 (15théorèmes/4définitions), BetaLimit23 (20/3), Integral10 (9/1).
Total44théorèmes et8définitions,52prints qualifiés. Core provient de ψ03 ; les
deux suivants de ψ04. Les reçus globaux FAIL correspondent aux modules suivants,
exclus de ce lot. Duplication n'est ni auditée ni compilée ici.

Core définit la vraie Ψ=Γ′/Γ et construit la limite des différences bêta à partir
de la dérivée du vrai quotient Γ(z)Γ(1+w)/Γ(z+w). BetaLimit paie le passage sous
l'intégrale : à gauche, le majorant2(t^(Re z−1)+1) contrôle le facteur bêta ; à
droite, un majorant de dérivée cpow sur[1/2,1] compense le facteur(1−t)^(w−1).
Le majorant concret total ajoute C(z)=‖z−1‖(1+(1/2)^(Re z−2)). Il est intégrable
sur(0,1) dès Re z>0. Mesurabilité du vrai intégrande, domination pour tout w≥0,
convergence ponctuelle et DCT sont construites avant l'identité Ψ bêta. Aucune
domination, integrabilité ou identité cible n'est donnée comme prémisse libre.

Integral paie t=exp(−u) : image exacte Ioi0→Ioo01, injectivité, dérivée signée
−exp(−u), valeur absolue du Jacobien, identité algébrique cpow/exp et transport
de l'intégrabilité. P1 est la vraie égalité, pour Re z>0,
Ψ(z)=−γ_E+∫_(u>0)(exp(−u)−exp(−zu))/(1−exp(−u))du.
Le théorème intermédiaire de changement de variables, valable pour tout z,
porte les intégrales Bochner totalisées ; l'intégrabilité du domaine Re z>0
est certifiée séparément. Aucun produit scalaire ou Fubini global n'en découle.

Ces conclusions analytiques auxiliaires ne paient pas C5/Arch, Fubini avec la
fonction test, duplication, Weil, contours infinis, compte complet des zéros,
coefficientN, D_N ou WIN. Le crible, Möbius, Vaughan, les formes bilinéaires
arithmétiques et les restes AP scalaires ne sont pas employés.

Préparation antérieure mono-Core dans le dossier parent : brouillon SOURCE
supersédé, jamais exécuté, aucun manifeste ni gate. Le présent dossier neuf
three_modules porte le seul gel batch04 ; aucun gel antérieur n'est modifié.
Helpers repris comme texte SOURCE, jamais par import/exécution d'ancien script.
Anciens lots Juge01/02/03 clos et leurs fichiers liés readonly,3089 archives
préservées. La seule dépendance locale des deux derniers modules est l'olean
neuf produit par le module précédent dans ce lot. Aucun olean auteur dans
LEAN_PATH, aucune recompilation de Γ′ ou d'ancien module.

Runtimes existants : Python4278cf… -B -X utf8 ; Lean4.15.0 8a1ef185… ; mathlib
9837ca9d65d9de6fad1ef4381750ca688774e608 et huit caches. Chaque import a source
et olean liés en SHA, avec Init implicite explicitement fermé. Sources et reçus
finaux/logs sont FULL ; API bêta TARGETED, grands manifestes HEADER/parse/SHA,
aucun FULL mathématique de toute la fermeture. Aucun banc numérique requis.

Gate ROOT neuve spécifique, un seul lanceur et batch04_attempt01, ordre
Core→BetaLimit→Integral, trois enfants au maximum, stop à la première erreur,
aucun retry, probe, replay, installation ou git. PRE/captures/START global et
module/commandes/logs/FIN/POST/receipt documentent l'essai ; les52prints doivent
être exacts et ne dépendre que de propext, Classical.choice et Quot.sound.

Base indépendante Γ′ :63modules/1057auxiliaires ; officiel après observation
ROOT seulement. Delta possible si trois audits PASS :3modules/52déclarations,
soit66/1109. Aucun crédit global H1, C3/C5, D_N ou WIN.
