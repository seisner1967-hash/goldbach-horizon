# Spécification native DIT/DIF — PAPER, aucun code exécutable

Tous les entiers ci-dessous sont exacts et les modularisations sont effectuées après les products avec intermédiaireuint64. Entrées/constantes/enclosures/certificats sont ceux du contrat projection_contract22_final.md. Ce document n'est pas un producteur ou checker SOURCE natif prêt. La source fixed_parameter_log_model22.py décrit seulement les vérifications des constantes et boîtes de log, sans aucune invocation.

## Producteur DIT par modulus

1. Vérifier les gardes de la table fixe p/c/g/omega, primalité et ordre ; vérifier l'inverseK et omega. Reconstituer le vecteur A_n à partir du catalogue et des records vérifiés, remplir0 pourN<n<K.
2. Permuter le vecteur en place par bit-reversal exactement sur27bits, chaque paire échangée une seule fois (index<reverse(index)). Vérifier0<=chaqueindex<K.
3. PourL=2,4,...,K, poserw_L=omega^(K/L) modp par exponentiation entière. Pourblock=0,L,2L,...,K-L :W=1 ; pourj=0..L/2-1 :
   u=A[block+j], v=A[block+j+L/2]*W modp ;
   A[block+j]=(u+v) modp ;
   A[block+j+L/2]=(u+p-v) modp ;
   W=W*w_L modp.
   Les bornes0<=u,v<p garantissent additions<2p et absence d'underflow avec u+p-v.
4. À la sortie, les données doivent être les F_j naturels. L'invariant DFT de chaque étage doit être prouvé, pas seulement déclaré par ce pseudocode.
5. h=omega^(-N) modp par inverse etpow entier. V=1, total=0 ; pourj=0..K-1 :
   total=(total+(A[j]^2 modp)*V) modp ; V=V*h modp.
   r_p=total*K_inverse modp ; vérifier0<=r_p<p. Écrire uniquementr_p et la provenance, pas le tableau de536MB.

## Checker indépendant DIF et reconstruction

1. Revalider le catalogue séquentiellement, la primalité par vrais témoins Lucas et les logs avec la boîte rationnellem40, puis reconstituer les points A_n. Revalider lui-même la tableNTT et tous les inverses ; aucune confiance dans les résidus du producteur.
2. Entrée en ordre naturel. PourL=K,K/2,...,2, avecw_L=omega^(K/L), pour chaqueblock poserW=1, puis parcourirj=0..L/2-1 :
   u=A[block+j], v=A[block+j+L/2] ;
   A[block+j]=(u+v) modp ;
   A[block+j+L/2]=((u+p-v) modp)*W modp ; W=W*w_L modp.
   La sortie est bit-reversed ; effectuer la permutation exacte27bits une fois, puis une réduction pondérée indépendante identique mathématiquement à la définition du résidu. Le checker réexécute tous les étages, sans validation par hash ou hasard.
3. CRT exact par Garner/Euclide :reconstruirec dans[0,Pi), vérifierc modp=r_p pour les cinq p, et0<=c<2^153. Refaire séparément le fold direct c_ref=sum(n=0..N)A_n*A_(N-n) avecuint192 ; imposerc=c_ref. Les productscross/arrondis natifs/largeurs des words ne sont pas sous-entendus :chaque product multiword doit avoir son contrôle/carry.
4. Après les deux vérifications de c_A entier (DIF et fold direct A), réutiliser le tableau des points pour reconstruire B_n, depuis de nouvelles boîtes log40 et leur milieu quantifié/clamp. Fold c_B entier, indépendamment des points A. Imposer |c_A-c_B|<=2(N+1)(64S+1), construire les deux rayons de vraieC_N par les logs reconstruits et l'enveloppeE, recalculer la garde2(N+1)(64S+1)*1000000<=S² par entiers, vérifiercataloguecomplet/logscounts/tablemoduli entière/resources, puis produire au mieux PAPER_AUDITED_EXACT_INTEGER_PROJECTION_AUX_PASS après future revue du producteur complet. Ce libellé n'est ni certification Lean des primitives ni identité spectraleglobale ni WIN. Le statut n'existe aujourd'hui qu'en proposition ; aucun PASS actuel. Un fold A exact seulement ne certifie pas les primitives ni le coefficient réel.

Les circuits de données producer/checker et leurs erreurs doivent être audités en SOURCE avant une préparation. Une unique répétition indépendante coûte réellement une seconde série de cinq transformées ; le format condensé des outputs n'autorise pas à l'omettre. Toute garde absente, rootcandidate échouée, overflow, loglarge, données noncouvertes ou manque de ressources ferme sans verdict mathématique.
