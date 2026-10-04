"""Coordinator bookkeeping only. Never executes an arithmetic bank or Lean."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json, subprocess

ROOT = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
HELPER = Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
BASE = [sys.executable, '-B', '-X', 'utf8', str(HELPER)]
COMMON = ['--cwd', str(ROOT), '--run-name', 'parity']
TREE = ROOT / '.arbor/sessions/parity/.coordinator/idea_tree.json'
CHECKPOINT = TREE.parent / 'checkpoint.json'

def invoke(command, *arguments, quiet=False):
    process = subprocess.run(BASE + [command] + COMMON + list(arguments), capture_output=True, text=True, encoding='utf-8')
    if not quiet or process.returncode:
        print(process.stdout, end='')
    if process.stderr:
        print(process.stderr, end='', file=sys.stderr)
    if process.returncode:
        raise SystemExit(process.returncode)

nodes = [
    ('13.6', 'agent1_weighted_incidence.md',
     'Mechanism: réindexer les images canoniques par d=cr≤a et conserver le masque semipremier centré sur les unités réelles.\n'
     'Hypothesis: la factorisation canonique permet une projection exacte et une norme écrite indépendante du masque ; la covariance couplée reste une obligation à estimer sans disponibilité supposée.\n'
     'Observable: progression entière d141, masque complet et première incidence réelle, covariance, second moment et gap Cauchy rationnels, fronts AP exacts et cinq raccords D/W neufs.\n'
     'Conflicts: aucune suppression de Γ ni substitution du masque par sa densité ; Type I/II non acquis, properpowers raw conservées, onset source distinct et aucun paiement global.'),
    ('13.7', 'agent2_signed_cofactors.md',
     'Mechanism: fusion de deux facteurs des petits cœurs composites complets, avec union physique des représentations et rang de parité.\n'
     'Hypothesis: pour une seule cible E de rang pair au moins4 par q, les vrais coefficients opposés réduisent le principal à un sélecteur de cibles sans partenaire ; cette incidence OR demeure à estimer.\n'
     'Observable: tous q premiers8000..8200, cible3003, union des six cofacteurs, vrais kernels actifs, comparaisons entières et par couple, multiplicité, cœurs premiers et e1 séparés.\n'
     'Conflicts: rang2 et e1 hors formule composite ; pas de capacité globale entre E, pas de signe réel déduit du principal, aucune disponibilité ou borne cible postulée.')
]

tree = json.loads(TREE.read_text(encoding='utf-8'))
assert not any(node_id in tree['nodes'] for node_id, _, _ in nodes), 'selection already exists; inspect instead of rerunning'
for node_id, report, hypothesis in nodes:
    invoke('add', '--parent-id', '13', '--hypothesis', hypothesis)
    tree = json.loads(TREE.read_text(encoding='utf-8'))
    assert tree['nodes'][node_id]['hypothesis'] == hypothesis
    invoke('update', '--node-id', node_id, '--status', 'running', '--insight', 'Selected arithmetic mechanism; numerical canonical checks available, independent Judge15 audit pending. No Lean bypass candidate or global estimate.')
    invoke('prompt-executor', '--node-id', node_id, '--workdir', str(ROOT), '--additional-context',
           'Continuation of the already dispatched six research roles; retrospective exact selection receipt, not new dispatch. Read round15/PROBE_BLOCK.md and round14_feedback.md. Respect 651 immutable historical artifacts. Audit ' + report + ' and the new strict bank only. Root remains coordinator. Freeze FINAL reports before independent Judge15 audit. No ordinary projection, local sign identity or target-shaped assumption counts as victory. No historical producer or Lean rebuild.', quiet=True)

checkpoint = json.loads(CHECKPOINT.read_text(encoding='utf-8'))
checkpoint['phase'] = 'ROUND15_FINAL_REPORTS_AND_INDEPENDENT_JUDGE_PREPARATION'
checkpoint['current_nodes'] = [x[0] for x in nodes]
checkpoint['in_flight_executors'] = [
    'round13_bilateral_ideation:role2 final corrected small-core fusion report',
    'round13_formal3_switch:role6 finalize three new strict banks and unique isolated receipts',
    'agent5_juge:independent readonly review, freeze awaiting FINAL2 and FINAL6'
]
checkpoint['last_progress'] += ' FINAL1_15 read and frozen SHA8fa44b44; new d141 complete incidence canonicalPASS/replay,695035 integers278014units4201beta912firstprime,GammaNEG49properpowers5D/Wsample. Necessary read-only stored-vector supplement certifies theta variance/Cauchy gapPOS and AP front X97999795 correction−35/23 without kernels. Fusion canonicalPASS/replay21q86labels78cores1680axes416profiles360primeparents7targets112edges71NEG41POSrealpairs,0orphans windowonly,248primeparents retained with composite target. Corrected provisional e1/F1 and Eevenrank≥4 domains before FINAL; no fabricated Lean failure. Nodes13.6/13.7 selected pending independent audit; no Lean15/global estimate/Win.'
checkpoint['previous_goal_turn_classification'] = 'progress'
checkpoint['previous_goal_turn_evidence'] += [
    'round15/agent1_weighted_incidence.md', 'round15/incidence_checks.py', 'round15/incidence.json',
    'round15/fusion_checks.py', 'round15/fusion.json', 'round15/incidence_moment_checks.py', 'round15/incidence_moment.json',
    'round15/role6/incidence_replay_receipt.json', 'round15/role6/fusion_replay_receipt.json',
    '.arbor/sessions/parity/experiments/13.6/executor_prompt.md', '.arbor/sessions/parity/experiments/13.7/executor_prompt.md'
]
CHECKPOINT.write_text(json.dumps(checkpoint, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print('ROUND15_SELECTION_RECORDED; independent audit pending; no producers or Lean called')
