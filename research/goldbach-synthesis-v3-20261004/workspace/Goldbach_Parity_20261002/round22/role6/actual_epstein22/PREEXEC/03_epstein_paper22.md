# Déroulement d'Epstein : contrat auxiliaire nouveau, avant exécution

Statut : source préparée seulement. Aucune importation Python mathématique, aucun calcul, aucun banc, aucune invocation Lean22. L'autorisation de préparer les sources est distincte de la sélection et de la porte d'exécution root. Ce document n'est pas une preuve Lean.

Pour y>0, m entier non nul, q=|m| et a=qy, considérer

    I(m,y)=∫₀¹ Σ(n∈Z) y^(3/2)/[(mx+n)²+(my)²]^(3/2) dx.

La série positive converge ; la majoration des indices éloignés permet Tonelli. Le changement u=mx+n transforme la somme d'intervalles en un recouvrement de R de multiplicité q presque partout. Le jacobien1/q compense exactement ce recouvrement. La primitive

    ∫(u²+a²)^(-3/2)du = u/[a² sqrt(u²+a²)]

donne I(m,y)=2/(m²sqrt(y)). Ce sont les modes m≠0 du vrai réseau d'Epstein ; le mode m=0, le facteur global1/2 dans E_full, sa normalisation par ζ(2s), l'équation différentielle et l'identification à la diffusion ne sont pas testés par ce banc. La définition non primitive de réseau est donnée par [Lagarias–Suzuki, équation(1)](https://arxiv.org/pdf/math/0412039). La preuve du présent déroulement utilise uniquement des changements continus de variable et le réseau entier.

La fenêtre symétrique exacte −Q≤n≤Q, Q>q, donne

    I_Q=y^(3/2)/(q a²) [Σ(u=Q+1..Q+q)H_a(u) − Σ(u=−Q..−Q+q−1)H_a(u)],
    H_a(u)=u/sqrt(u²+a²).

Les termes intérieurs de Σn[H(n+q)−H(n)] s'annulent comme une somme finie. Pour m<0, n↦−n conserve la fenêtre symétrique et le carré ; aucun déplacement de ses endpoints n'est effectué. ROLE2 a vérifié ces indices et le facteur sur papier. Pour18cas originaux, le producteur évalue séparément chaque intégrale aux2Q+1 indices, puis la formule aux2q endpoints ; ces deux intervalles doivent se rencontrer. Pour6cas d'échelle, la formule finie réduit algébriquement les2Q+1 indices représentés à2q endpoints effectivement évalués. Le résultat distingue ces deux comptes ; il ne prétend pas avoir évalué individuellement les indices d'échelle.

Pour |n|>Q, |mx+n|≥|n|−q. Les deux queues sont ainsi majorées par

    0≤I−I_Q≤2y^(3/2)Σ(n>Q)(n−q)^(-3)
                    ≤2y^(3/2)∫_Q^∞(u−q)^(-3)du
                    =y^(3/2)/(Q−q)².

Cette enveloppe fermée continue est valable sur y>0,Q>q ; les paramètres de ce banc sont fixés avant gel. Les18cas originaux sont y∈{1/2,1,2}, m∈{−7,−2,−1,1,2,7}, Q=4096. Les6cas supplémentaires ont y=Y=10000=√100000000, les mêmes m et Q=2^20. Pour ces derniers, Q−q>10^6 et y^(3/2)=10^6 donnent une queue <10^(-6) par une inégalité entière. La tolérance globale est1/100000 pour chacun des24cas. L'échelle N est exercée par Y ; aucun coefficient additifN n'est calculé.

Le nouvel évaluateur `interval22.py` représente un intervalle par deux entiers divisés par2^96. Addition et soustraction sont exactes sur cette grille ; multiplication et division arrondissent vers l'extérieur. Pour sqrt(x), isqrt de l'entier mis à l'échelle donne le plancher exact, et un test carré donne le plafond. À chaque appel, les deux inégalités carrées sont vérifiées en entiers et leurs coordonnées rationnelles sont émises dans `epstein_sqrt_certificates22.jsonl`, avec un compte par cas et un hash de fichier dans le reçu. Le dénominateur exclut0, le radicand est positif, et le reste ajouté n'élargit que le bord supérieur, puisque la queue est positive. Aucun Float, décimal approché ou ancienne bibliothèque arithmétique n'est utilisé. Ces opérations demandent encore leurs preuves Lean si un certificat formel est revendiqué.

Contre-test fixé : pour q>1, multiplier la cible entière parq, simulant l'oubli de la compensation du recouvrement. L'intervalle mutant doit être disjoint de l'intervalle calculé ; les cas q=1 sont consignés comme non applicables, sans être retirés. Un chevauchement trop large est UNRESOLVED_NON_INFORMATIVE. Une disjonction sur l'identité originale n'est annoncée qu'avec les gardes et la provenance des enclosures ; ce serait un échec auxiliaire à diagnostiquer. Un éventuel EPSTEIN_UNFOLDING_AUX_PASS signifierait contrôle numérique de cette couche avec la tolérance déclarée, sans compilation ni victoire globale.

Le protocole futur utilise un seul sous-processus nouveau, une source et un runtime liés par SHA, captures PREEXEC antérieures au lancement, actual_START/commande/log/exit/reçu et vérification POSTEXEC séparée. Le lanceur consomme atomiquement l'unique tentative après porte root exacte. Il ne crée pas de résultat pendant la préparation et n'effectue pas un second préflight de conservation. Les3089archives et la conservation21 historique ne sont pas réexécutées.
