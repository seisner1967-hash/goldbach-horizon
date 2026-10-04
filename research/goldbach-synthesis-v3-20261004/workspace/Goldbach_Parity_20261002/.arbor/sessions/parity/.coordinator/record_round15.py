"""Record already completed FINAL15 evidence; no arithmetic or compiler runs."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
from hashlib import sha256
import json, subprocess

ROOT = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
COORD = ROOT / '.arbor/sessions/parity/.coordinator'
HELPER = Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
COMMON = [sys.executable, '-B', '-X', 'utf8', str(HELPER)]
def invoke(command, *arguments, quiet=False):
    p = subprocess.run(COMMON + [command, '--cwd', str(ROOT), '--run-name', 'parity'] + list(arguments),
                       capture_output=True, text=True, encoding='utf-8')
    if not quiet or p.returncode: print(p.stdout, end='')
    if p.stderr: print(p.stderr, end='', file=sys.stderr)
    if p.returncode: raise SystemExit(p.returncode)
def read(path): return json.loads(path.read_bytes())
controller_path = ROOT / 'round15/controller_manifest.json'
assert controller_path.exists(), 'Root FINAL15 binding must already have succeeded'
controller = read(controller_path)
assert controller['round'] == 15 and controller['victory'] is False and controller['score'] == 0
assert controller['no_test_reexecution_by_controller']
controller_sha = sha256(controller_path.read_bytes()).hexdigest()
count = len(controller['bindings_sha256']) + 1
next_count = 651 + count
tree = read(COORD / 'idea_tree.json')
old_root = tree['nodes']['ROOT']['insight']
assert tree['nodes']['13.6']['status'] == tree['nodes']['13.7']['status'] == 'running'
notes = {
 '13.6': ('agent1_weighted_incidence.md',
  'Judge15 readonly exit0 confirms actual canonical d=cr<=a mask, unit projection and centered norm, with complete d141 bank695035 integers278014units60982prime axes4201beta912prime images, GammaNEG. 49rawproperpowers including4masked retained; five new actualD/W samples only,907unsampledWerrors unpaid. Necessary frozen-vector L4 supplement certifies variance/gapPOS and APX97999795 correction−35/23, three full identical copies total. Written Chebyshev/cardinality/norm and BV dyadic reconstruction K_N are valid partial reductions; no estimate for aggregate Gamma or comparison to true parent incidence, extraBVonsetunknown. No Lean15/noWin; exactmask→density false finite promotion only, valid covariance method remains available.'),
 '13.7': ('agent2_signed_cofactors.md',
  'Judge15 readonly validates corrected actual F1 coree>=2 with e1separate, F2–F5 targetevenrank>=4/parentcompositeoddrank>=3. Complete J1 cores give U=0/D=0/C=±W, primecore keepsLambda. For one E/q, entire principal majorized by explicit real-prime orphan selector F4; F6 and global reuse remain unestimated. Complete21q window yields86labels78cores1680vertices416profiles360primeparents7targets112edges,248parents retained with composite target,400prime labels are360physical capacities. Entire Delta/B NEG but actualpairs71NEG41POS vs112principalNEG. Zeroorphans onlyNO_COUNTEREXAMPLE_IN_WINDOW; no universal availability. Finite rank/J2caps no sourceNoGo. No Lean15; valid fusion/OR route retained, narrow labels/sign promotions false only.')
}
for node_id, (report, insight) in notes.items():
    invoke('record', '--node-id', node_id, '--report-file', str(ROOT / 'round15' / report), '--score', '0',
           '--insight', insight, '--result', 'Partial arithmetic reduction; independent FINAL15 audit passed, analytic obligation open; no victory.',
           '--code-ref', str(ROOT / 'round15' / report))
new_root = (
 'Goal active, no victory. Judge15 unique readonly audit exit0 after FINAL1/2/6:39 frozen production inputs35numericbindings3fullbyte+field identical copies,4localfalsifiers and1NO_COUNTEREXAMPLE_IN_WINDOW,1138rational sign positions (1131certificates+7moment/AP intervals),zero floats/unresolved. No actual failed numerical or Lean attempt in15; corrected provisional e1/E-rank guards before freeze not compiler errors. Cumul15modules208aux unchanged. Canonical shortconductor d=cr<=a exposes genuine semiprime mask beta without nprimefilter; written Chebyshev bound/norm valid, aggregate covariance Gamma stillunestimated. Complete d141 bank695035 integers278014units60982prime axes4201beta912prime images,GammaNEG,49rawproperpowers4masked;5D/Wraccord samples only,907unsampledWerrors unpaid. Necessary read-only L4/AP supplement certifies variance/CauchygapPOS, X97999795/front−35/23; no kernels/PASSrerun. BV cumulative keepsdyadicK_N/front and additionalonsetunknown; TypeII conditions not shown. Smallcomplete J1core fusion F1e>=2/e1exception andF2–F5Eevenrank>=4,compositeoddrank>=3. Entire oneE/q principal<=explicit first-prime orphan mass F4; F6/globalparentreuse not estimated. Full21qwindow86labels78cores1680vertices416profiles360primeparents7targets112edges,248primeparents with composite target retained. Delta/BentireNEG, actualpairs71NEG41POS despite112principalNEG;0orphans only finite no counterexample.400prime labels count360physicalvertices; finite6factor/J2c<=9 cuts no asymptoticNoGo.651oldpreserved; root15binds' + str(count-1) + '+self' + str(count) + ', SHA' + controller_sha + '; nextprotected' + str(next_count) + '.\n'
)
old_root = old_root.split('\nNext15 must seek')[0]
new_root += old_root + (
 '\nNext16 must seek independent quantitative control of the weighted real Gamma covariance or coupled OR incidence with global physical capacities. Do not postulate availability/density/target bounds; do not compile standard projection/norm, generic OR expansion or local fees as a bypass. Keep lowconductors and actual TypeII product ranges distinct; broader signed complement/source ledger intact. All old' + str(next_count) + ' archives immutable; genuine new strict numerical tests only after candidate selection.'
)
invoke('update', '--node-id', 'ROOT', '--insight', new_root)
invoke('meta', '--set', 'eval_cmd=powershell -NoProfile -ExecutionPolicy Bypass -File ' + str(ROOT / 'round15/judge/audit-judge.ps1'),
       '--set', 'dataset_info=FINAL15 unique independent readonly audit exit0;39inputs35numericbindings3identicalcopies4localfalsifiers1138signpositions;15modules208aux;sourceu>=10^24;nextprotected' + str(next_count) + ';noWin;16pending')
checkpoint_path = COORD / 'checkpoint.json'
checkpoint = read(checkpoint_path)
checkpoint.update(phase='ROUND15_COMPLETE_ROUND16_INTAKE', rounds_completed=15,
                  current_nodes=[], in_flight_executors=[], objective_complete=False, victory=False,
                  last_judge_receipt='round15/judge/judge_receipt.json',
                  last_controller_manifest='round15/controller_manifest.json', last_controller_manifest_sha256=controller_sha,
                  next_protected_artifacts_expected=next_count, next_protected_registry_pending=None,
                  previous_goal_turn_classification='progress', external_blocker=None)
checkpoint['last_progress'] = new_root.split('\n')[0] + ' Nodes13.6/13.7 recorded done0, valid mechanisms retained; feedback15 and strict artifacts pending.'
checkpoint['previous_goal_turn_evidence'] = list(dict.fromkeys(checkpoint['previous_goal_turn_evidence'] + [
    'round15/agent2_signed_cofactors.md','round15/agent6.md','round15/numeric_manifest.json','round15/role6_final_receipt.json',
    'round15/agent5.md','round15/judge/judge_receipt.json','round15/judge/audit_launch_receipt.json','round15/controller_manifest.json'
]))
checkpoint_path.write_text(json.dumps(checkpoint, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
report_path = ROOT / 'REPORT.md'
report = report_path.read_text(encoding='utf-8')
report = report.replace('au cours de quatorze boucles', 'au cours de quinze boucles', 1)
report = report.replace('Aucun Lean supplémentaire n\'est appelé en14 faute de candidat quantitatif.',
                         'Les boucles14/15 n\'appellent aucun Lean supplémentaire faute de candidat quantitatif ;15 conserve une covariance réelle et un sélecteur de cibles sans partenaire.', 1)
report = report.replace('## Reprise active : boucle 15', '## Boucle 15 : covariance du masque et fusion des petits cœurs, estimations ouvertes', 1)
report = report.replace('le Juge indépendant prépare son audit, en attente du rapport numérique FINAL.',
                        'le Juge indépendant a terminé son audit unique des rapports finaux.', 1)
report = report.replace('Pièces en attente de clôture indépendante :', 'Pièces mathématiques finales :', 1)
report = report.replace('la cible a−W', 'la cible a pour coefficient−W', 1)
report += (
 '\n### Clôture indépendante15 et poursuite\n\n'
 '**Audit indépendant unique exit0 ; victoire fausse.** Les trois rapports et39 productions finales sont gelés. Le Juge vérifie35 liaisons numériques, trois copies isolées identiques en champs/octets et1138 positions rationnelles de signe :1131 certificats et sept intervalles du supplément L4/AP. Ces compteurs ne sont pas de nouveaux théorèmes. Quatre promotions finies sont réfutées ; la disponibilité des partenaires n\'a aucun contre-exemple dans la fenêtre et demeure non prouvée universellement. Aucun producteur PASS, ancien banc, Lean, dépendance ou rendu PDF n\'est rejoué par le Juge ou root. Il n\'y a aucun véritable essai numérique ni Lean échoué en15 ; les deux corrections de domaine sont antérieures au gel.\n\n'
 'Les651 archives et PDF/ZIP originaux restent intacts. Root lie' + str(count-1) + ' fichiers15 et son controller constitue le fichier' + str(count) + ', SHA' + controller_sha + '. Le prochain inventaire protège' + str(next_count) + '=651+' + str(count) + ' fichiers. Les nodes13.6/13.7 sont enregistrés done0 avec leurs obligations ouvertes, sans éliminer les mécanismes valides. Le contrôle strict des artefacts est effectué après génération du rapport d\'arbre.\n\n'
 'Pièces : [Juge15](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/agent5.md), [reçu indépendant](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/judge/judge_receipt.json), [manifeste root](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/controller_manifest.json), [rapport numérique](D:/Users/Utilisateur/Desktop/Maths/Goldbach_Parity_20261002/round15/agent6.md). La recherche reste active vers l\'estimation couplée de Γ ou de F6 après union ; D_N≤N/(256u ell) reste ouvert.\n'
)
report_path.write_text(report, encoding='utf-8')
print('ROUND15_RECORDED; next protected', next_count, '; no tests or compiler called')
