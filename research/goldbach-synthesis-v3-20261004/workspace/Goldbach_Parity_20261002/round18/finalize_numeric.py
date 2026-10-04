"""FINAL6 collation of frozen stored artifacts; never imports or runs a producer."""
import sys
sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
ROLE = ROOT / 'role6'
REGISTRY_SHA = '05212665afffecade91134e1533f93d11eba8058179198e4420eef1fe252f2bc'


def digest(path):
    h = sha256()
    with Path(path).open('rb') as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8'))


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + '\n', encoding='utf-8')


def certificates(value, path=''):
    if isinstance(value, dict):
        if {'sign', 'lower', 'upper'} <= set(value):
            yield path, value
        for key, child in value.items():
            yield from certificates(child, path + '/' + str(key).replace('~', '~0').replace('/', '~1'))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from certificates(child, path + '/' + str(index))


def main():
    assert not (ROOT / 'role6_final_receipt.json').exists(), 'FINAL6 already frozen'
    assert digest(ROOT / 'previous_artifacts_sha256.json') == REGISTRY_SHA
    preflight = load(ROOT / 'conservation.json')
    preflight_receipt = load(ROLE / 'conservation_attempt01_receipt.json')
    assert preflight_receipt['exit_code'] == 0 and preflight['files'] == 997
    assert preflight['changed'] == {} and preflight['added'] == preflight['removed'] == []
    assert preflight_receipt['conservation_sha256'] == digest(ROOT / 'conservation.json')
    banks, replay_hashes, canonical_hashes, indices = {}, {}, {}, {}
    total = {'POSITIVE': 0, 'NEGATIVE': 0, 'ZERO': 0}
    perbank = {}
    for bank in ('typeii', 'semiprime'):
        canonical_path = ROOT / (bank + '.json')
        canonical = load(ROLE / (bank + '_canonical_receipt.json'))
        replay_path = ROOT / ('isolated_' + bank) / (bank + '.json')
        replay = load(ROLE / (bank + '_replay_receipt.json'))
        assert canonical['canonical_pass'] and canonical['exit_code'] == 0
        assert replay['status'] == 'PASS_UNIQUE_ISOLATED_REPLAY' and replay['exit_code'] == replay['comparison_exit_code'] == 0
        assert replay['bytes_identical'] and replay['all_fields_identical']
        assert digest(canonical_path) == canonical['output_sha256'] == replay['output_sha256'] == digest(replay_path)
        assert canonical_path.read_bytes() == replay_path.read_bytes()
        data = load(canonical_path)
        assert data == load(replay_path) and data['victory'] is False and data['strict_rational_only'] is True
        banks[bank] = data
        replay_hashes[bank] = digest(ROLE / (bank + '_replay_receipt.json'))
        canonical_hashes[bank] = digest(ROLE / (bank + '_canonical_receipt.json'))
        counts = {'POSITIVE': 0, 'NEGATIVE': 0, 'ZERO': 0}
        index = []
        for pointer, cert in certificates(data):
            lo, hi = Fraction(cert['lower']), Fraction(cert['upper'])
            assert lo <= hi
            sign = cert['sign']
            assert sign in counts
            assert (sign == 'POSITIVE' and lo > 0) or (sign == 'NEGATIVE' and hi < 0) or (sign == 'ZERO' and lo == hi == 0)
            counts[sign] += 1
            total[sign] += 1
            encoded = json.dumps(cert, sort_keys=True, separators=(',', ':')).encode()
            index.append({'json_pointer': pointer, 'sign': sign, 'stored_certificate_sha256': sha256(encoded).hexdigest()})
        assert len({row['json_pointer'] for row in index}) == len(index)
        perbank[bank] = {'positions': len(index), 'signs': counts}
        indices[bank] = index
    assert perbank == {'typeii': {'positions': 98, 'signs': {'POSITIVE': 40, 'NEGATIVE': 25, 'ZERO': 33}},
                       'semiprime': {'positions': 222, 'signs': {'POSITIVE': 151, 'NEGATIVE': 58, 'ZERO': 13}}}
    assert sum(total.values()) == 320
    save(ROLE / 'certificates_index.json', {'status': 'STORED_CERTIFICATE_PATH_INDEX', 'banks': indices,
                                           'counts_by_bank': perbank, 'combined_counts': total,
                                           'producer_kernel_or_logarithmic_sign_recalculation': False})
    typeii, ss = banks['typeii'], banks['semiprime']
    actual_attempts = []
    for bank, numbers in [('typeii', [1]), ('semiprime', [1, 2])]:
        for number in numbers:
            path = ROLE / f'{bank}_attempt{number:02d}_receipt.json'
            item = load(path)
            actual_attempts.append({'bank': bank, 'attempt': number, 'exit_code': item['exit_code'],
                                    'receipt_sha256': digest(path), 'log_sha256': item['log_sha256']})
    assert [v['exit_code'] for v in actual_attempts] == [0, 1, 0]
    failure = load(ROLE / 'semiprime_attempt01_failure.json')
    assert failure['identity_false'] is False and failure['classification'] == 'TECHNICAL_OUTPUT_ENCODING_INTERFACE'
    measures = {key: value['sign_certificate']['sign'] for key, value in ss['selected_measures'].items()}
    ss_pp = ss['properpowers_retained']
    summary = {'round': 18, 'status': 'FINAL6_BOTH_CANONICAL_PASS_TWO_UNIQUE_ISOLATED_REPLAYS_IDENTICAL',
               'protected_inventory_preflight': 997, 'canonical_attempts': actual_attempts,
               'canonical_new_bank_invocations': 3, 'actual_numeric_failures': 1,
               'actual_false_arithmetic_identities': 0, 'isolated_new_bank_replay_invocations': 2,
               'isolated_replay_exit_codes': [0, 0], 'canonical_receipts_sha256': canonical_hashes,
               'isolated_replay_receipts_sha256': replay_hashes, 'certificate_counts_by_bank': perbank,
               'combined_sign_counts': total, 'strict_sign_positions': 320,
               'SS_selected_measure_signs': measures,
               'all_target_proper_power_axis_count': len(ss_pp['all_target_proper_power_axes']),
               'resource_proper_power_axis_count': len(ss_pp['resource_proper_power_axes']),
               'SS_excluded_class_raw_proper_power_count': len(ss['switch_completeness']['excluded_class_raw_proper_power_catalog']),
               'old_rounds1_through17_mathematics_replayed': False,
               'Lean_called': False, 'global_D_N': False, 'score': 0, 'victory': False}
    save(ROLE / 'numeric_summary.json', summary)
    report = f'''# FINAL6 — boucle18, deux contrats neufs conservés

Les deux banques canoniques sont PASS, avec exactement un rejeu isolé autorisé chacune. Les copies sont identiques octet par octet et champ par champ. Cette clôture numérique ne certifie aucun contournement de parité : score0, victoirefausse, aucun Lean lancé par le rôle6.

## Conservation et invocations réelles

Le préflight unique a réellementexit0 : inventaire997=799+198, zéro changement/ajout/retrait et deux documents originaux préservés. Le registreSHA est `{REGISTRY_SHA}`. Ses source pré-exécution, commande, log et reçu restent dans `role6/conservation_attempt01*`. L'état d'attente initial `preflight_status.json` est conservé comme capture d'une phase antérieure, pas comme statut présent.

Trois invocations canoniques neuves réelles : TypeII01 exit0 ; SS01 exit1 technique ; SS02 exit0. Deux invocations isolées neuves réelles : TypeII exit0 et SS exit0. Aucun ancien producteur, kernel, signe, PASS, olean ou PDF des boucles1–17 n'a été rejoué. Les seuls kernels répétés sont les nouveaux18 du stade SS inachevé, puis son unique rejeu explicitement autorisé. Chaque invocation possède un marqueur exclusif, un snapshot avant subprocess, sa commande, son log et son exit effectif. Sources/helpers/launchers canoniques demeurent figés aprèsPASS.

L'échec SS01 est précis : le masque q utilisait un générateur ; le helper gelé `bithex` attend une séquence avec `len`. Après les54 nouveaux kernels et286 triplets validés, l'encodage final levait TypeError. L'unique réparation transforme ce générateur en liste ; elle ne modifie aucune garde, factorisation, racine, identité ou signe. Source/log/diagnostic échoués restent archivés. SS02 reprend ce stade neuf inachevé. Ce n'est pas une identité arithmétique fausse ni un diagnostic de parité.

## TypeII d91, contrat entier

Tous109890 b de879121..989010 sont conservés, avec j=N−91b dans10000090..19999989. Beta={typeii['beta_structural']['A']} sans filtre premier j ; theta={typeii['progression_complete']['theta_candidate_count']} ; rawproperpowers={typeii['raw_Lambda_N']['unit_proper_power_count']}. La base propre de candidats va jusqu'à4472, les caps q/s sont physiques et complets. Tous v11..20 et57189 couples réels sont testés ; les colonnes w sont disjointes. Les multiplicités analytiques de j restent, sans créer une capacité.

E17/19 est le résultat de la vraie garde gcd sur tous les entiers ; kappa modulo1001, classes216/948, est construit avant theta. R1 sur le bloc entier possède son coefficient de signe par colonne ; ce certificat est distinct du témoin périodique R2. J0h39/429=27050/24591 ; J91h39/429=23185/21077. JR11=273/234. R2,R7,R8 et le carré complet de calibration sont exacts. T normalisés=109200000/541 et936000000/4637 ; deux dépassements stricts de x/log²x réfutent uniquement la promotion finie pour tous coefficients dans cette fenêtre. Les références429 annulent ce témoin mais en gardent tout le prix L11. Prix theta,II,II_raw et raw demeurent distincts ; R9/R10 et toutes les puissances propres sont conservés. Aucun Γ agrégé ni TypeII entier n'est majoré.

## SS, double extraction et union physique

Fenêtre fermée5001 entiers q1400100..1405100 ;333 premiers unitaires,22 cœurs SF unitaires >3 jusqu'à70,7326 axes complets. Demandes theta A258,R32,S674 ; S=SS40+reste634. Quatorze q ont réellement deux ressources semipremières. Les286 triplets distincts donnent des divisions CRT entières, six déterminants orientés vérifiés et les racines effectives de leur nouveau polynôme à chaque premier≤100. Les gardes de cible, les formes non primitives hors garde, rho1 aux témoins, rho4 seulement hors Delta_switch et les saturations restent visibles. Selberg fini T3/Y1 est construit sur ces nouvelles racines, avec les deux +1 et les lcm conservés ; aucun D5/D10/D11 source n'est appliqué.

L'union comporte68 vertices physiques :54 kernels actifs nouveaux et14 axes m0 exactement nuls, laissés littéraux. Les40 demandes SS et14 ressources m1 sont fusionnées par leur entier m. Chaque kernel actif du PASS est évalué une fois. Deux m1 sont des ancres p0 déjà présentes, sans crédit supplémentaire. Le premier axe de m0 vaut3q : theta et raw Lambda_N sont exactement0. Lambda(e), les deux signes mu, originalQ, k1, strictak<m, wholeU_a et le bas≤alpha sont conservés. Les profiles horsSS et leurs vrais W restent littéraux nonpayés.

Signes des mesures sélectionnées stockées : `{json.dumps(measures, ensure_ascii=False, sort_keys=True)}`. Ils portent uniquement sur la fenêtre et le sous-ensemble sélectionnés. Properpowers de tous axes cibles={len(ss_pp['all_target_proper_power_axes'])}, properpowers ressources={len(ss_pp['resource_proper_power_axes'])}, properpowers dans les classes exclues SS={len(ss['switch_completeness']['excluded_class_raw_proper_power_catalog'])}. Une absence finie ne devient pas un théorème source. Aucun mu(n)^2 ne filtre le premier axe.

Quatre falsifiers locaux SS : SS=S entier ; capacité raw non nulle pour m0 ; rho4 sur un témoin de L ; primitivité de n_e sans exclusions. Ils ne réfutent aucun résultat source ni une possibilité globale. Les634 demandes de S horsSS, T_A et l'assignation des capacités uniques restent ouverts.

## Certificats, copies et portée

320 positions de certificats stricts stockés, sans flottant :191POS,83NEG,46ZERO. TypeII98=40POS25NEG33ZERO ; SS222=151POS58NEG13ZERO. Le fichier `role6/certificates_index.json` donne chaque JSONpointer et le hash du certificat existant ; la clôture lit les bornes rationnelles, sans recalculer un kernel ni une expression logarithmique. Les positions répétées pour un même témoin sont des positions stockées distinctes, pas des expérimentations supplémentaires.

Sortie TypeII `{digest(ROOT / 'typeii.json')}` ; sortie SS `{digest(ROOT / 'semiprime.json')}`. Reçus isolés TypeII `{replay_hashes['typeii']}` etSS `{replay_hashes['semiprime']}`. Copies `isolated_typeii/typeii.json` et `isolated_semiprime/semiprime.json` intégrales, égales aux canoniques. Le manifeste lie les sources, snapshots, logs, reçus, sorties, index et ce rapport ; le reçu final lie ce manifeste.

Onset source logN≥10^24 ; budget SS écrit logN≥10^36, segment intermédiaire nonpayé. N10^8 ne teste ni l'un ni l'autre. Acquis16/17 et ledger D_N=Bprime^a+Bpp^a+Pband≥2+Zface≥2+Ialpha+2max(e,0) maintenus. Aucune cible globale démontrée. Seul le Juge Lean indépendant peut certifier les nouveaux théorèmes ; même un PASS auxiliaire demeure distinct de la condition de victoire.
'''
    (ROOT / 'agent6.md').write_text(report, encoding='utf-8')
    roots = ['conservation.py', 'conservation.json', 'previous_artifacts_sha256.json', 'PROBE_BLOCK.md',
             'agent1_calibrated_typeii.md', 'agent2_capacity_incidence.md', 'agent6.md',
             'typeii_checks.py', 'typeii.json', 'semiprime_checks.py', 'semiprime.json', 'finalize_numeric.py',
             'isolated_typeii/typeii.json', 'isolated_semiprime/semiprime.json']
    excluded = {'role6/finalize_attempt01.log', 'role6/finalize_attempt01_receipt.json', 'role6/closure_receipt.json'}
    paths = [ROOT / name for name in roots]
    paths.extend(p for p in ROLE.rglob('*') if p.is_file() and p.relative_to(ROOT).as_posix() not in excluded)
    bindings = {p.relative_to(ROOT).as_posix(): digest(p) for p in sorted(set(paths))}
    reports = {name: bindings[name] for name in ['agent1_calibrated_typeii.md', 'agent2_capacity_incidence.md', 'agent6.md']}
    manifest = {'round': 18, 'status': 'FINAL6_FROZEN_NUMERIC_BINDINGS', 'files': len(bindings), 'sha256': bindings,
                'reports_FINAL_sha256': reports, 'canonical_new_bank_invocations': 3, 'actual_numeric_failures': 1,
                'unique_isolated_replays': 2, 'both_copies_bytes_and_all_fields_identical': True,
                'strict_sign_positions': 320, 'sign_counts': total, 'counts_by_bank': perbank,
                'preflight_protected_inventory': 997, 'role6_FINAL_receipt_path': 'role6_final_receipt.json',
                'finalizer_log_receipt_and_closure_bound_separately_after_actual_exit': True,
                'Lean_called': False, 'global_D_N': False, 'victory': False}
    save(ROOT / 'numeric_manifest.json', manifest)
    final_bindings = dict(bindings)
    final_bindings['numeric_manifest.json'] = digest(ROOT / 'numeric_manifest.json')
    final_receipt = {'round': 18, 'status': 'FINAL6', 'score': 0, 'victory': False,
                     'report_sha256': bindings['agent6.md'], 'numeric_manifest_sha256': final_bindings['numeric_manifest.json'],
                     'bound_files': len(final_bindings), 'sha256': final_bindings,
                     'canonical_receipts_sha256': canonical_hashes, 'isolated_replay_receipts_sha256': replay_hashes,
                     'strict_sign_positions': 320, 'sign_counts': total, 'actual_numeric_failures': 1,
                     'old_producer_kernel_sign_Lean_PDF_replayed': False,
                     'closure_receipt_follows_actual_finalizer_exit': True}
    save(ROOT / 'role6_final_receipt.json', final_receipt)
    print(json.dumps({'status': 'FINAL6', 'manifest_files': len(bindings), 'final_receipt_bound_files': len(final_bindings),
                      'report_sha256': bindings['agent6.md'], 'numeric_manifest_sha256': final_bindings['numeric_manifest.json'],
                      'final_receipt_sha256': digest(ROOT / 'role6_final_receipt.json'), 'sign_positions': 320,
                      'sign_counts': total, 'actual_numeric_failures': 1, 'unique_isolated_replays': 2,
                      'SS_measure_signs': measures, 'victory': False}), flush=True)


if __name__ == '__main__':
    main()
