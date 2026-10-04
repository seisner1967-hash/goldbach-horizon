# ROLE4 — contrat source Γ′ et transport des boîtes, boucle22

Statut SOURCE_ONLY pour Γ′/boîtes. La base H2 a trois compilations réelles distinctes : deux échecs, puis Gamma3 sortie0 avec23audits standards et0sorryAx, encore en attente du Juge indépendant. Les nouveaux modules GammaDerivative22.lean et GammaBoxBounds22.lean n'ont été ni compilés ni préparés pour une invocation. Aucun banc Γ′, aucune valeur de centre complexe et aucune boîte de zéro ne sont évalués ici. Le banc Gamma21cas595b1534 ne valide pas les nouveaux théorèmes de dérivée ou de transport ; il n'est pas rejoué.

Le premier module emploie la vraie Γ et la formule de Cauchy du cache4.15, avec un contour fermé de rayon1/2. Si1≤Re(s)≤2, tout le disque fermé reste dans Re(z)>0, où la différentiabilité de la vraie Γ est justifiée par l'exclusion de ses pôles. Le cercle appartient au strip[1/2,5/2]. La convexité Gamma et Γ(1/2)=√π donnent Γ réelle≤9/5 sur ce strip, Γ(5/2)=3√π/4 ; la rotation ±π/4 déjà construite donne un coefficient≤3, donc

    |Γ(w)|≤(27/5) exp(-(π/4)|Im(w)|).

Sur le cercle |Im(w)-Im(s)|≤1/2, l'amortissement est majoré par exp(π/8)≤7/4, d'où le dominateur concret

    |Γ(w)|≤(189/20) exp(-(π/4)|Im(s)|).

La vraie intégrale de Cauchy divise ce majorant par le rayon1/2. Elle donne189/10≤19 et la source énonce

    |Γ′(s)|≤19 exp(-(π/4)|Im(s)|), 1≤Re(s)≤2.

Aucune formule de dérivée sous une intégrale tournée n'est supposée. Le majorant sur le cercle, la différentiabilité dans le disque et la continuité sur sa fermeture sont des preuves explicites proposées. La méthode diffère de la dérivation Laplace papier1+16+2, mais fournit la même constante19 et la même interface finale. ROLE3 a relu FULL la première version8lemmes2cbd2d33 dans9a0734 et n'a identifié aucun trou mathématique. Le pont rpow et les transferts norm/re/im ont ensuite été explicités ; la version finale est relue FULL58b04e et reste non compilée.

Le second module définit le vrai terme

    H_Y(rho)=exp(log(Y)*rho) Γ(rho+1), Y>0,

avec raccord proposé à la puissance principale (Y:ℂ)^rho. Pour Y≥1 et le domaine convexe0≤Re(rho)≤1, Im(rho)≥gammaLo≥0, la différentiation du produit, H2 et le nouveau majorant Γ′ donnent

    |H_Y′(rho)|≤C(Y,gammaLo)
    C=Y exp(-(π/4)gammaLo)(19+2logY).

Le théorème des accroissements finis normé du cache opère directement surℂ et le domaine convexe réel ; aucune projection scalaire arithmétique n'est employée. Pour rho et un centre rho0 dans ce domaine, |Re(rho-rho0)|≤deltaBeta et |Im(rho-rho0)|≤deltaGamma impliquent

    |H_Y(rho)-H_Y(rho0)|≤R_box
    R_box=C(Y,gammaLo)(deltaBeta+deltaGamma).

Cette expression est fermée, non négative pour des demi-largeurs non négatives, et conjointement continue pourY>0 ; ces trois charges ont des preuves source dédiées. Le module final12déclarations/12audits est relu FULL64b2cc, puis ROLE3 FULLfa0e5f à SHA82dd6682d0912decfa22adbcf022dbed6343c8d7cb71bca748a3f064b8443ea0, sans trou mathématique identifié en relecture source. L'évaluation numérique future doit ajouter R_box au rayon certifié du calcul au centre. Les erreurs de logY, de Γ au centre, des phases et produits restent à propager séparément. Une multiplicité m paie m fois le rayon ; une paire conjuguée paie les deux contributions, après preuve de conjugaison.

ÀN=10^8 etY=10000, l'interfaceROLE6 propose des demi-largeurs≤2^-80, gammaLo>0 et jusqu'à1000 contributions comptées avec multiplicité/conjugaison. Le budget de localisation papier780000000/2^80<2^-50 dépend explicitement du compte réel encore ouvert. Les nouvelles sources ne prouvent aucune existence ou complétude des boîtes, n'assument pas RH et n'acceptent pas des centres décimaux comme zéros exacts.

Un futur banc informatif Γ′/Rbox exige un nouveau producteur, ses domaines et restes fermés, des cas fixes et mutations discriminantes, des références indépendantes et une gate numérique distincte. Il doit tester la normalisation exponentielle des dérivées et le transport de centres rationnels avec phases des deux signes ; une tolérance absolue qui masque les modes hauts ne suffit pas. Aucun tel banc n'est déclaré PREPARED ou PASS ici. L'ancien banc H2 et G0 ne sont pas des oracles Γ′.

H1 vraie trace Weil, tous les vrais zéros/multiplicités avec compte et complétude certifiés, Stieltjes H3, les moments/queues restants et l'intégrale archimédienne restent des couches distinctes. Ces preuves auxiliaires source ne démontrent aucune annulation globale de Goldbach, ne paient pas le coefficientN ou D_N et n'accordent aucune victoire. Le ledger et logN≥10^24 sont conservés.
