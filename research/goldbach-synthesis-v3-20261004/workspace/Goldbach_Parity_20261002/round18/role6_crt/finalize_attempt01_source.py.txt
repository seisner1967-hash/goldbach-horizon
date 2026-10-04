"""Metadata-only FINAL6CRT closure.  Reads stored facts, never a producer."""
import sys
sys.dont_write_bytecode = True
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path

ROLE = Path(__file__).resolve().parent
ROUND = ROLE.parent
ROOT = ROUND.parent


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as handle:
        json.dump(value, handle, indent=2, sort_keys=True, ensure_ascii=False)
        handle.write('\n')


def main():
    for name in ['manifest.json', 'final_receipt.json']:
        assert not (ROLE / name).exists()
    report_path = ROUND / 'agent6_crt.md'
    assert not report_path.exists()
    canonical = json.loads((ROLE / 'canonical_receipt.json').read_text(encoding='utf-8'))
    assert not (ROLE / 'replay_receipt.json').exists()
    assert not (ROLE / 'replay_authorization.json').exists()
    assert canonical['exit_code'] == 0
    assert canonical['canonical_pass'] is True
    assert digest(canonical['output']) == canonical['output_sha256']
    bank = json.loads(Path(canonical['output']).read_text(encoding='utf-8'))
    registry = json.loads((ROLE / 'input_registry.json').read_text(encoding='utf-8'))
    for name, binding in registry['inputs'].items():
        assert digest(binding['path']) == binding['sha256'], name
    report = f'''# FINAL6CRT — annexe rationnelle indépendante, boucle18 node13.10

Le contrat CRT neuf est PASS après une seule invocation canonique. Zéro rejeu : aucun rejeu n'a été autorisé ni exécuté ; le Juge doit vérifier séparément les comptes et les fractions stockés. Les sources, helpers, launcher, contrat et entrées sont inchangés. Ceci valide des identités auxiliaires et les données d'un banc fini ; score0, victoirefausse, aucun contournement global de parité.

## Invocations réelles et provenance

Canonique : {canonical['started_at_utc']} à {canonical['finished_at_utc']}, exit{canonical['exit_code']}. Zéro échec et zéro rejeu de cette annexe. Captures PREEXEC exclusives, commande réelle, cwd, sources/helpers/launcher/contrat/registre et onze entrées copiées avant subprocess ; marqueur, log et reçu réels conservés. Le code exécuté est une copie neuve capturée. Aucun ancien producteur, W/D/kernel, prix ou signe logarithmique, Lean, préflight ou PDF n'a été relancé ou importé. Le FINAL6 initial et ses67/68 liaisons restent gelés ; ce FINAL6CRT est séparé. PREPARED.md et contract.json restent des captures historiques du stade antérieur au lancement, pas un état actuel. La voie replay préparée dans le launcher n'a pas été activée.

TypeII.json est lu comme données gelées, SHA {registry['inputs']['typeii']['sha256']}. A={bank['structural_A_read_only']} vient du catalogue beta structurel, avec196 entiers m distincts, sans filtre de primalité du candidat. Les comptes J/JR sont calculés indépendamment par les prédicats entiers puis comparés aux champs stockés scope91:h39 ; aucun prix ni expression logarithmique n'est recalculé.

## Objets effectifs et contrôles complets

N=100000000,d91,h39,ell11,V10,x20000000,Ioc(879120,989010),L109890. H={bank['H']},K={bank['K']}. Trialdivision déterministe complète, facteurs et produits exacts, tous diviseurs avec leurs exposants et Möbius exact. H a972 diviseurs dont32 squarefree ; K1944 dont64. Tous les diviseurs de Möbius nul sont conservés. deltaH=96/455=phi(H)/H, frontH32 ; deltaK=192/1001=960/5005=phi(K)/K, frontK64. La positivité et les fronts comme comptes squarefree sont contrôlés rationnellement.

Chaque indicatrice d'unité de tous109890 b est vérifiée contre l'inclusion-exclusion exacte. Les counts de multiples/floors et leurs fronts≤1 sont conservés pour chacun des972/1944 diviseurs. J(H)={bank['J_source_H']},J(K)={bank['corrected_H_times_ell']['J']}. Tous les entiers11..20 sont testés par gcd(v,K) ; E={bank['E_all_integer_unit_rows']}, résultat de la garde d'unité, sans supposition que v soit premier. Le front de E et #E≤V sont vérifiés avec les1944 diviseurs de K.

Pour chacun des972 k|H et chacune des2 lignes réelles, les inverses sont obtenus par Euclide avec Bézout vérifié. Une recherche indépendante des v possibilités prouve l'unicité de la classe modulo k*ell*v. L'ensemble complet des multiples k*ell vérifiant d*b≡N modv est comparé à l'ensemble complet de la classe CRT dans I. Cette égalité d'ensembles prouve l'équivalence sur tout l'intervalle, puis les counts/floors exacts et le front rationnel≤1. Les1944 contrôles, y compris mu(k)=0, sont publiés individuellement.

Les lignes réelles donnent124 b pour v17 et110 pour v19 ; leurs inclusions-exclusions et fronts≤32 concordent. JR={bank['JR_direct_sum_of_rows']} est leur somme, avec234 couples (v,b) stockés. Le catalogue garde les multiplicités analytiques ; il ne crée aucune capacité physique.

## Gardes R4/R5 et référence corrigée

R4a :128≤1920/1001 est FAUX. R4b :32≤2109888/91 est VRAI. R4c :320≤4603392/91091 est FAUX. Ces valeurs sont des prémisses indépendantes, pas des identités mises en échec. Toutes les identités CRT/IE/fronts sont vraies. Puisque deux gardes échouent, R5 n'est pas appliqué sur ce banc. Les comparaisons observées234≥4603392/91091 et234/23185≥12/11011 restent des observations finies ; elles ne prouvent pas les gardes ni un énoncé source.

La référence corrigée H*ell donne J21077 etJR0. Sa garde gcd(ell,H*ell)=1 est fausse, puisque gcd=11 ; l'ancien minorant ne s'y applique pas. Le zéro concorde avec le champ corrigé gelé, sans recalcul de sa somme ou de son prix.

## Portée, empreintes et clôture

Count source {registry['inputs']['Count']['sha256']} ; Lower {registry['inputs']['Lower']['sha256']}. Sortie canonique {canonical['output_sha256']}. Reçu canonique {digest(ROLE / 'canonical_receipt.json')}. Zéro reçu de rejeu, aucun fichier replay produit. Le manifeste séparé lie sources, captures, gate canonique, log, reçus, sortie, rapport et onze entrées readonly ; son reçu final distinct lie le manifeste. La clôture ajoute les liaisons effectives du processus de métadonnées, après son exit réel.

Aucune nouvelle position de signe logarithmique : les320 positions initiales restent inchangées. Le régime source logN≥10^24, les fronts exponentiels/totient source et R6 ne sont ni testés ni supposés à N10^8. Gamma global, D_N et l'agrégation physique restent ouverts. Les acquis, les997 archives et le ledger entier sont préservés. L'annexe ne compile aucun théorème et n'annonce aucune victoire ; le Juge indépendant demeure responsable du contrôle Lean.
'''
    with report_path.open('x', encoding='utf-8', newline='\n') as handle:
        handle.write(report)
    excluded = {'manifest.json', 'final_receipt.json', 'closure_receipt.json',
                'finalize_attempt01.log', 'finalize_attempt01_receipt.json'}
    owned = {str(path.relative_to(ROOT)): digest(path)
             for path in sorted(ROLE.rglob('*')) if path.is_file() and path.name not in excluded}
    owned[str(report_path.relative_to(ROOT))] = digest(report_path)
    readonly = {str(Path(binding['path']).relative_to(ROOT)): binding['sha256']
                for binding in registry['inputs'].values()}
    manifest = {'state': 'FINAL6CRT_AUXILIARY_ONLY', 'round': 18, 'node': '13.10',
                'owned_artifacts_sha256': owned, 'read_only_inputs_sha256': readonly,
                'owned_bindings_count': len(owned), 'readonly_bindings_count': len(readonly),
                'canonical_output_sha256': canonical['output_sha256'],
                'isolated_replay_count': 0, 'replay_authorized': False, 'new_log_sign_positions': 0,
                'metadata_only_no_mathematical_expression_executed': True,
                'score': 0, 'victory': False}
    manifest_path = ROLE / 'manifest.json'
    save(manifest_path, manifest)
    final_bindings = {**owned, **readonly,
                      str(manifest_path.relative_to(ROOT)): digest(manifest_path)}
    receipt = {'state': 'FINAL', 'finished_at_utc': datetime.now(timezone.utc).isoformat(),
               'round': 18, 'role': '6_CRT_annex', 'node': '13.10',
               'manifest': str(manifest_path.relative_to(ROOT)), 'manifest_sha256': digest(manifest_path),
               'report': str(report_path.relative_to(ROOT)), 'report_sha256': digest(report_path),
               'bindings_sha256': final_bindings, 'bindings_count': len(final_bindings),
               'actual_numeric_attempts': 1, 'actual_numeric_failures': 0,
               'canonical_exit': 0, 'isolated_replays': 0, 'isolated_replay_exit': None,
               'replay_authorized': False,
               'all_inputs_readonly_unchanged': True, 'new_log_sign_positions': 0,
               'old_producers_replayed': 0, 'W_D_kernels_executed': 0,
               'Lean_executed': 0, 'R5_applied_under_false_premises': False,
               'R6_proved_or_assumed': False, 'global_D_N_controlled': False,
               'score': 0, 'victory': False}
    save(ROLE / 'final_receipt.json', receipt)
    print(json.dumps({'state': 'FINAL6CRT_METADATA_PREPARED', 'owned': len(owned),
                      'readonly': len(readonly), 'final_bindings': len(final_bindings),
                      'report_sha256': digest(report_path),
                      'manifest_sha256': digest(manifest_path),
                      'receipt_sha256': digest(ROLE / 'final_receipt.json'), 'victory': False}, sort_keys=True))


if __name__ == '__main__':
    main()
