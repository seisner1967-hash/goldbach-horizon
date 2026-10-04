# ROLE4 — préparation 2 Gamma, node 15.2

Statut : SOURCE_ONLY, aucun compilateur, API probe, calcul Gamma ou banc Python exécuté. Le module Gamma contient vingt théorèmes et trois définitions, chacun accompagné d'une commande `#print axioms` qualifiée. Il n'est pas encore un module vérifié.

## Énoncé concret

`Gamma_strip_exponential_bound` porte sur le vrai `Complex.Gamma s` et les seules hypothèses géométriques `1 ≤ s.re ≤ 2` :

    ‖Complex.Gamma s‖ ≤ 2 exp(-(π/4)|s.im|).

La source construit l'intégrabilité de l'intégrande `exp(-z*t)t^(s-1)` pour `Re(s)>0`, `Re(z)>0`, sa dérivée en z et le dominateur local `exp(-(Re(z)/2)t)t^Re(s)`. L'identité de Laplace complexe est dérivée par analyticité sur le demi-plan droit et accumulation des taux réels positifs en 1. La rotation principale `z=exp(iθ)`, `|θ|<π/2`, donne le facteur `exp(-θ Im(s))`. Le cas θ=π/4 utilise la log-convexité réelle de Gamma prouvée par Hölder dans le cache, puis la conjugaison couvre les hauteurs négatives. Aucune formule de Laplace complexe ou borne H2 n'est un paramètre de la conclusion.

La formule primaire [DLMF 5.9.1](https://dlmf.nist.gov/5.9.E1), lue ciblée, confirme les domaines `Re(ν)>0`, `Re(z)>0` et les puissances principales. Le cache fournit seulement la formule à taux réel positif ; c'est pourquoi l'extension complexe est construite dans ce module. Les API de dérivation paramétrique acceptent un corps `𝕜` RCLike, donc ℂ, malgré le commentaire local qui cite ℝ.

## Limites et obligations ouvertes

Les sources n'ont pas été élaborées : la preuve peut nécessiter des réparations d'API, de coercions ou de tactiques après ouverture d'une porte de compilation. Aucun échec Lean n'est encore enregistré. Les modules de queues restent séparés et en cours ; leurs premières expressions continues et prérequis pointwise ne prouvent pas encore leurs queues intégrées.

H1 (la vraie formule globale de Weil), le compte global des vrais zéros avec multiplicité, les boîtes complètes/Turing et la quadrature archimédienne restent des obligations. Le module Gamma ne prouve ni H1, ni le compte, ni le coefficient N, ni le bilan D_N. Le seuil source `log N≥10^24` est conservé ; N=10^8 est seulement le test fini demandé. Aucun outil arithmétique interdit par la directive22 n'est utilisé.

## Porte future

Le premier banc Γ appartient à ROLE6 : vingt et un cas sigma∈{1,3/2,2}, gamma∈{0,±1,±10,±100}, évaluation par Laplace tournée et référence indépendante des normes via réflexion Gamma. Les rayons de primitives, queues et quadrature doivent être fermés avant sa propre autorisation root. Son statut exact, son reçu réel et ses SHA doivent être relus par root. Le PASS G0 Epstein n'ouvre pas la porte Gamma.

Le lanceur de cette préparation refuse de fonctionner sans une autorisation root séparée, liée au manifeste de préparation, à la source, à un résultat Γ informatif réellement produit et aux binaires existants. L'exécution future conserve PREEXEC, commande, environnement Lean, sorties brutes, code sortie et reçu. Une compilation sans erreur devra ensuite être contrôlée par un Juge indépendant. Aucun WIN n'est demandé sur ce seul module auxiliaire.



Incident de métadonnées conservé : préparation1 a parcouru3185 modules mais a pris dix fragments JavaScript/commentaires pour des imports Lean. Elle garde le statut PREPARATION_DEPENDENCY_OPEN et ses fichiers intacts. Préparation2 utilise un scanner lexical des commentaires imbriqués, chaînes ordinaires et chaînes brutes. Il s'agit d'une réparation de traçabilité, sans essai mathématique ou invocation Lean. Le lanceur2 refuse explicitement un manifeste de dépendances ouvert.

