"""Once-only FINAL5 metadata from the completed independent audit; no math run."""
import sys
sys.dont_write_bytecode = True
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROUND = HERE.parent
BASE = ROUND.parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def save(path, value):
    with Path(path).open('x', encoding='utf-8', newline='\n') as f:
        json.dump(value, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write('\n')


def main():
    a = load(HERE / 'audit_receipt.json')
    launch = load(HERE / 'launch_receipt.json')
    inputs = load(HERE / 'input_manifest.json')
    assert launch['exit_code'] == 0 and launch['audit_receipt_sha256'] == sha(HERE / 'audit_receipt.json')
    assert a['status'] == 'PASS_INDEPENDENT_ROUND18_AUXILIARY_AUDIT'
    counts = a['new_counts']
    assert counts == {'modules': 8, 'theorems': 170, 'defs': 68, 'structures': 4, 'instances': 0, 'axioms_printed': 242}
    assert a['cumulative_counts'] == {'modules': 30, 'theorems': 507}
    assert a['preservation_before']['files'] == a['preservation_after']['files'] == 997
    assert a['victory'] is False and a['score'] == 0
    assert len(inputs['round18_sha256']) == 267 and len(inputs['historical_dependencies_sha256']) == 22
    assert len(list((HERE / 'preexec').iterdir())) == 11
    table = []
    warnings = []
    for row in a['independent_Lean']['modules']:
        assert row['status'] == 'PASS_FRESH_NEW_LEAN' and row['exit_code'] == 0
        assert sha(row['olean']) == row['olean_sha256'] and sha(row['log']) == row['log_sha256']
        c = row['declaration_counts']
        table.append(f"| {row['module']} | {c.get('theorem', 0)} | {c.get('def', 0)} | {c.get('structure', 0)} | {row['axioms_printed']} | 0 |")
        warnings.extend(row['actual_style_warnings'])
    assert len(warnings) == 1 and "warning: 'push_cast' tactic does nothing" in warnings[0]
    report = ROUND / 'agent5.md'
    text = f'''# FINAL5 — Juge indépendant, boucle 18

Verdict réel : huit nouvelles compilations indépendantes PASS, 170 théorèmes auxiliaires, aucune victoire. Le contrôle du contenu porte sur les hypothèses et conclusions effectives ; il ne confond pas la compilation d'un ingrédient conditionnel avec un contournement global de parité.

L'audit autorisé a commencé à {launch['started_at_utc']} et s'est terminé à {launch['finished_at_utc']}, exit0. Les scripts d'audit, les nouvelles sources, les 267 inputs et les 22 dépendances historiques sont liés avant les subprocess ; 11 captures PREEXEC exclusives précèdent l'audit. Les huit sources ont été compilées une seule fois dans judge/build, avec leurs dépendances nouvelles compilées par le Juge. Les oleans auteurs18 ne figurent pas dans LEAN_PATH ; les dépendances historiques sont readonly et n'ont pas été recompilées. Lean 4.15.0 est lié au SHA 8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08 ; le cache mathlib fourni est lié au commit 9837ca9d65d9de6fad1ef4381750ca688774e608 et à ses huit bibliothèques.

| Nouveau module | Théorèmes | Définitions | Structures | Prints d'axiomes | Exit |
|---|---:|---:|---:|---:|---:|
{chr(10).join(table)}

Total neuf : 8 modules, 170 théorèmes, 68 définitions, 4 structures, 0 instance et 242 prints. Chaque déclaration explicite a son print, y compris les déclarations sans axiomes. Les seuls axiomes admis sont propext, Classical.choice et Quot.sound ; aucune occurrence active de sorry, admit, axiom ad hoc, native_decide, sorryAx ou trustMe. Le seul warning indépendant est le push_cast inactif prévu de Count ; son exit0 et ses axiomes restent vérifiés. Aucun échec du Juge, aucune continuation et aucun stage PASS rejoué. Le cumul des acquis auxiliaires devient 30 modules et 507 théorèmes (ancien cumul 22/337).

## Données finies et provenance

Les 997 fichiers historiques, leur inventaire exact et les documents originaux sont préservés avant et après l'audit. Les FINAL et les échecs auteurs restent figés. Les 23 invocations auteurs contiennent 15 échecs techniques conservés ; ils ne sont pas des preuves d'un blocage de parité. Les sorryAx générés dans certains logs échoués sont invalides et n'ont pas servi. L'incident du premier finalizer ROLE3 est une erreur de lecteur de cinq prints sans axiomes, capturée POSTEXEC et conservée, puis corrigée comme métadonnées sans compilation supplémentaire.

Le Juge a lu les 320 positions de certificats rationnels stockés : 191 positifs, 83 négatifs, 46 nuls. Il a contrôlé leurs bornes strictes et les deux copies TypeII/SS déjà rejouées, sans évaluer de kernel W/D, logarithme, prix ou expression de signe. Les contrôles entiers ont porté sur les supports complets, les facteurs, les masks, les produits effectifs et leurs multiplicités, les classes CRT, les 22 cœurs SF unitaires et les 286 switches nouveaux. Les gardes SS peuvent être fausses ; rho=4 n'est utilisé que hors actualDelta sous les conditions réelles. Les axes zéro ou non évalués n'ont pas reçu de kernel fictif. Les 7326 demandes gardent A258, R32 et S674=SS40+634 hors SS.

L'annexe distincte CRT a une seule invocation canonique et zéro replay. Le Juge en a contrôlé les 35/11 bindings de manifeste, les 47 du reçu et les 10 de clôture, ainsi que l'exit réel du finalizer metadata. Il a vérifié indépendamment tous les diviseurs et fractions/fronts stockés, les 1944 checks CRT, les unités complètes et les lignes réelles v17/v19. J=23185, JR=234 ; R4a/R4b/R4c=faux/vrai/faux. R5 n'est pas appliqué malgré deux comparaisons finies vraies. Pour H*ell, JR=0 et la garde de coprimalité échoue. Aucune nouvelle position de signe, aucune exécution d'un producteur ou helper numérique, ancien préflight ou PDF, aucune ancienne compilation.

## Contenu et condition de victoire

La reindexation TypeII provient d'une bijection des produits effectifs (v,w) vers les incidences (v,b). Son identité normalisée et le minorant R5 restent adversariaux locaux, avec leurs prémisses arithmétiques indépendantes ; ils ne majorent pas D_N et ne contrôlent pas Gamma première entière. La correction du conducteur annule le témoin, mais conserve toute l'ancienne somme dans son prix. Theta, raw Lambda sans mu(j)^2 et les multiplicités bilinéaires restent distincts.

La double extraction construit les quotients, divisions, racines et nouveaux poids Selberg effectifs. La borne finie conserve la double somme de tous les restes, la saturation et les inputs indépendants. La revue du contenu distincte lie 37 pièces et a été lue intégralement. Les nouveaux énoncés n'introduisent pas la cible globale comme prémisse, mais leur application source demeure à fermer : R4/R6, SS vers roughCell aux fronts effectifs, uniformité CRT+1, sommation des paramètres, Mertens/totient et les inputs analytiques, D5/D10/D11. Le seuil écrit SS reste logN>=10^36, alors que le source fixé commence à10^24 ; le segment intermédiaire n'est pas payé. Le reste634, T_A, l'assignation unique des capacités, les prix et Gamma agrégée restent ouverts.

Le ledger fixé reste D_N=Bprime^a+Bpp^a+Pband>=2+Zface>=2+Ialpha+2max(e,0). Aucun nouveau théorème ne ferme ce ledger ni D_N<=N/(256 logN loglogN). Score0, victoirefausse, aucun NoGo global. Les échecs techniques documentés ont été réparés ; le blocage mathématique subsiste dans les raccords et l'agrégation globale.

Audit receipt SHA : {sha(HERE / 'audit_receipt.json')}. Les reçus de chaque subprocess, captures, logs et stages PASS sont liés par le manifeste du Juge et sa clôture metadata distincte après exit réel.
'''
    with report.open('x', encoding='utf-8', newline='\n') as f:
        f.write(text)
    excluded = {'manifest.json', 'final_receipt.json', 'closure_receipt.json',
                'finalize_attempt01.log', 'finalize_attempt01_receipt.json'}
    owned = {p.relative_to(BASE).as_posix(): sha(p) for p in sorted(HERE.rglob('*'))
             if p.is_file() and p.name not in excluded}
    owned[report.relative_to(BASE).as_posix()] = sha(report)
    manifest = {'status': 'FINAL_JUDGE18_AUXILIARY_NO_WIN', 'round': 18, 'role': 5,
                'owned_artifacts_sha256': owned, 'owned_files': len(owned),
                'frozen_round18_inputs_sha256': load(HERE / 'input_manifest.json')['round18_sha256'],
                'historical_dependencies_sha256': load(HERE / 'input_manifest.json')['historical_dependencies_sha256'],
                'original_documents_sha256': load(HERE / 'input_manifest.json')['original_documents_sha256'],
                'old_997_registry_sha256': sha(ROUND / 'previous_artifacts_sha256.json'),
                'new_counts': counts, 'cumulative_counts': a['cumulative_counts'],
                'independent_new_Lean_invocations': 8, 'independent_new_Lean_failures': 0,
                'CRT_replays': 0, 'kernel_log_sign_recalculated': False, 'score': 0, 'victory': False}
    save(HERE / 'manifest.json', manifest)
    save(HERE / 'final_receipt.json', {'status': 'FINAL5_AFTER_COMPLETED_ACTUAL_AUDIT',
         'round': 18, 'role': 5, 'finished_utc': datetime.now(timezone.utc).isoformat(),
         'report': report.relative_to(BASE).as_posix(), 'report_sha256': sha(report),
         'manifest': 'round18/judge/manifest.json', 'manifest_sha256': sha(HERE / 'manifest.json'),
         'audit_receipt_sha256': sha(HERE / 'audit_receipt.json'), 'audit_exit_code': launch['exit_code'],
         'independent_new_Lean_invocations': 8, 'independent_new_Lean_failures': 0,
         'new_counts': counts, 'cumulative_counts': a['cumulative_counts'],
         'new_numeric_producer_invocations': 0, 'CRT_replays': 0, 'old_997_preserved': True,
         'score': 0, 'victory': False, 'global_D_N_target_proved': False})
    print(json.dumps({'report_sha256': sha(report), 'manifest_sha256': sha(HERE / 'manifest.json'),
                      'final_receipt_sha256': sha(HERE / 'final_receipt.json'), 'owned_files': len(owned),
                      'score': 0, 'victory': False}), flush=True)


if __name__ == '__main__':
    main()
