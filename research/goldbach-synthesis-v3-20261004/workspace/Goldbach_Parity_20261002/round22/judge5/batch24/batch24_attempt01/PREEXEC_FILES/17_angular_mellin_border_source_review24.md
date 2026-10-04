# Revue indépendante SOURCE — BORD03 / futur lot24

Verdict : SOURCE_COHERENT_AFTER_THREE_TECHNICAL_REPAIRS_NOT_ELABORATED. Aucun PASS anticipé ; aucune compilation, import de candidat, sonde de tactique/API ou évaluation numérique pendant cette revue. Le lot23 reste clos, avec zéro crédit ; baseline ROOT82modules/1367déclarations.

La source gelée `D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round22/role4/angular_mellin_border_source03/AngularMellinBorder22.lean`, SHA1fa9de9a41a432b3745d1dce719018452e6f8f9b183bb9635d07191f1dcf91da, et contrat/catalogue sont lus FULLbe6f00. Reads/handoff sont lus FULL36a3f1. Les cinq SHA sont recontrôlés physiquement70792e. Le catalogue manuel exact demeure30déclarations22thm8defs/30prints qualifiés, neuf imports Mathlib et zéro dépendance locale.

Comparaison SOURCE manuelle avec le précédent FULL97715c/820903 et le vrai log23 FULL94f926 : les définitions, les énoncés, les domaines et l'ordre des prints restent inchangés. Seuls les trois corps de preuve correspondant aux diagnostics réels sont réparés. Les résultats du module précédent ne sont pas utilisés comme preuve compilée.

- Ancienne ligne80 : `change` expose maintenant la lambda exponentielle et sa valeur dérivée avant la normalisation associative/commutative du produit. Les deux fonctions ont bien la même expression `exp(-N*I*t)` ; la dérivée reste issue de `hb.cexp.comp_ofReal`, sans dérivée finale offerte en prémisse.
- Ancienne ligne116 : `rw [← inv_pow]` transforme l'inverse d'une puissance en puissance de l'inverse. La signature primaire cache `Mathlib/Algebra/Group/Basic.lean409–426`, SHA21b7cf8215c2960bca0d19a9c82e146e2b8ab12ae3a03d5298c136d2323a5ddd, est lue TARGETED18979e : `inv_pow(a): a⁻¹^n=(a^n)⁻¹`. L'inverse de−1 se simplifie ; aucune positivité ni hypothèse de signe de N supplémentaire n'est introduite.
- Ancienne ligne176 : `change ... at h` réduit explicitement la lambda de `congrArg` en produits par I, avant `rw [he] at h`. La balance reste dérivée de FTC ; la division reste conditionnée par N>0, qui fournit le cast non nul.

La chaîne mathématique déjà revue SOURCE est conservée : a>0 donne une base dans le slit-plane pour tout theta réel ; q est complexe quelconque ; dérivées puis continuités paient les deux IntervalIntegrable volume sur[-pi,pi]. FTC conserve les deux bords et les caractères valent(-1)^N. La récurrence divisée est J(q)=B(q)+(q/N)J(q+1). Le bord q=0 est nul ; q=1 vaut−(-1)^N/[N(a²+pi²)] et est non nul pour N>0. Aucune périodicité de cpow, aucune non-nullité universelle du bord ou intégrabilité finale libre n'est présumée.

Les API de la revue23 ce0fd2e… restent des lectures TARGETED antérieures, non un FULL du cache. La nouvelle source est cohérente avec les trois raccords demandés, mais la future élaboration peut encore échouer. Le compilateur est seul habilité à confirmer une olean indépendante et les axiomes des trente déclarations ; les prints SOURCE ne sont pas des résultats compilés.

Provenance gelée : contrat b3dd4b1809bcb599562ede96504887b58a0d3c818bc7f8562a50e9875c830760 ; catalogue379c32c142a3e3c157952d9f789b8618b7ffa4574b23e19d7a0db5188d50bee8 ; reads9149bccf45d1c8ffc188bfc58770fa3cf100b7ccf58193bbe696e57500acd2c5 ; handoff669b60c692fc9534d9ac0de5318c4f8b854b013ff1d57e10a309c57d2cc9a243.

ROOT23 clos est lu FULL70792e : observation dd5537597c002dee69a88c392d04dbfc787e7ab8dfcbdd684c46cabde7313863, statut INDEPENDENT_BATCH23_FAILED,0nouveau module/0déclaration. Log réel a9c287bf…/receipt38d1b67c…/adjudication222e7cdb…/completion47e22ee2… restent intacts. La nouvelle préparation24 doit être distincte, tous fichiers sous une même source root, sans olean auteur ni ancien module sur LEAN_PATH ; aucun metadata builder avant lecture ROOT FULL, aucun Lean avant une gate24 spécifique.

La conclusion reste auxiliaire finie. Mellin complexe global, corrélation spectrale, annulation signée, coefficient N=10^8, corrections PP/front/ledger, cible D_N et WIN ne sont pas acquis par cette révision.
