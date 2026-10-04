"""Coordinator selection bookkeeping only; no arithmetic bank or Lean invocation."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json, subprocess, hashlib

ROOT = Path(r'D:\Users\Utilisateur\Desktop\Maths\Goldbach_Parity_20261002')
HELPER = Path(r'C:\Users\Utilisateur\.codex\skills\arbor-agent-tools\scripts\arbor_state.py')
COMMON = ['--cwd', str(ROOT), '--run-name', 'parity']
BASE = [sys.executable, '-B', '-X', 'utf8', str(HELPER)]
COORD = ROOT / '.arbor/sessions/parity/.coordinator'

def invoke(command, *arguments, quiet=False):
    p = subprocess.run(BASE + [command] + COMMON + list(arguments), capture_output=True, text=True, encoding='utf-8')
    if not quiet or p.returncode:
        print(p.stdout, end='')
    if p.stderr:
        print(p.stderr, end='', file=sys.stderr)
    if p.returncode:
        raise SystemExit(p.returncode)

nodes = [
    ('13.8', '13', 'agent1_bilinear_covariance.md',
     'Mechanism: calibrer le masque semipremier reel par la divisibilite du candidat j=N-77sq modulo3, avec correction litterale de la reference uniforme.\n'
     'Hypothesis: la vraie AP sur q donne un defaut TypeI3 de taille principale pour le centrage uniforme au source ; la correction locale garde Gamma residuelle et prix parent-image entiers.\n'
     'Observable: progression entiere neuve d77, tous beta/classes/unites/theta/rawproperpowers, drifts exacts et Gamma=Gamma_corrigee+L3 ; preuve ecrite T1-T6 independante.\n'
     'Conflicts: ni condition TypeI entiere ni TypeII/Gamma/C16 estimees ; pas de remplacement S(bN), pas de signe fini source impose, aucun gain de norme compte comme victoire.'),
    ('14.1', '14', 'agent2_or_incidence.md',
     'Mechanism: coupler le plus petit premier impair absent de N au produit singulier reel puis au coefficient physique du coeur premier.\n'
     'Hypothesis: pour Npair positif, les facteurs locaux forces donnent S(N)-logp0>=1/144, puis C_p0q<=-1/288 au source sur vrais points bulk premiers, sans disponibilite supposee.\n'
     'Observable: derivation Euler-tail-harmonique et formalisation du vrai produit, fenetre neuve complete q1000100..1000300 avec tous coeurs SFunit<=98, kernels et capacites physiques depensees une fois.\n'
     'Conflicts: enclosure source acquise explicite, pas de marge postulee ni S libre ; incidences/F6/union globale non estimees, e1 et Lambda(e) conserves, signes finis non deduits de U4.')
]

tree_path = COORD / 'idea_tree.json'
tree = json.loads(tree_path.read_text(encoding='utf-8'))
assert not any(n[0] in tree['nodes'] for n in nodes), 'Selection already exists; inspect instead of rerunning.'
role1 = ROOT / 'round16/agent1_bilinear_covariance.md'
assert hashlib.sha256(role1.read_bytes()).hexdigest() == 'f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754'
for node_id, parent, report, hypothesis in nodes:
    invoke('add', '--parent-id', parent, '--hypothesis', hypothesis)
    tree = json.loads(tree_path.read_text(encoding='utf-8'))
    assert tree['nodes'][node_id]['hypothesis'] == hypothesis
    invoke('update', '--node-id', node_id, '--status', 'running', '--insight',
           'Selected new arithmetic mechanism. Complete new numerical contract authorized; execution pending. Anchor formalization dispatched. No global parity bypass or victory.')
    invoke('prompt-executor', '--node-id', node_id, '--workdir', str(ROOT), '--additional-context',
           'Exact selection receipt for already dispatched six research roles, not new dispatch. Read round16/PROBE_BLOCK.md and round15_feedback.md. Protect all701 old productions. Audit round16/' + report + '. Only the two new selected contracts may execute. Root remains coordinator. A7 must derive the actual singularSeries/tprod with tail and Euler-harmonic obligations; no margin-shaped input or prime availability. Preserve actual source onset and rawproperpowers. No historical bank/Lean reruns. Independent Judge after FINAL reports and frozen outputs.', quiet=True)

message = '''# Selection ROOT16

After fresh constraints and full reading of both conceptual reports, select node13.8 (local TypeI drift/correction) and node14.1 (least missing prime anchor).

Role1 FINAL SHA f60827e9e72e73cde93512448bd6acc289807d43180b844040326456a5e2d754. Role2 conceptual FINAL is pending at selection; its final hash will be bound separately. No numerical result is presumed.

Bank1: the entire d77 progression I_b1038962..1168831; genuine beta without candidate-prime filter; all local classes/units, theta and rawproperpowers; exact old/corrected drifts, Gamma correction and physical AP fronts. No D/W required for this incidence-only question. No source estimate applied at N1e8.

Bank2: test all201 integers q1000100..1000300 and retain genuine prime units; all SF/unit cores1..98 under the actual cap, theta/raw kept separate, active physical D/W and necessary controls; affine principal enclosure and actual coefficients distinct. e1/e3 physical capacities are each spent once; total positive demand, resource13, other resources and the whole signed sum remain distinct. No fabricated availability, extra mass or sign.

Each new bank may run one canonical attempt and one isolated copy after PASS. Preserve every real failed source/log if any; never attribute a missing analytic estimate to a nonexistent Lean failure. No old producer or PASS gate is rerun. All701 historical productions and originals stay immutable.

Formalizer3 is dispatched for actual product/convergence/tail/finiteEuler/A7. Formalizer4 will handle harmonic/logarithmic margin and small cases after role2 FINAL releases a slot. Source C2 enclosure is an explicit acquired input; the desired margin is not an input. The coefficient anchor is a partial result, not a win absent the full independent incidence estimate.
'''
(COORD / 'messages/round16_selection.md').write_text(message, encoding='utf-8')
checkpoint_path = COORD / 'checkpoint.json'
cp = json.loads(checkpoint_path.read_text(encoding='utf-8'))
cp['phase'] = 'ROUND16_SELECTED_NUMERICS_AND_ANCHOR_FORMALIZATION'
cp['current_nodes'] = [n[0] for n in nodes]
cp['in_flight_executors'] = [
    'round13_formal3_switch:role6 two selected new complete numerical contracts',
    'round13_bilateral_ideation:role2 conceptual FINAL freeze',
    'round16_formal3_anchor:role3 actual Euler-tail and singularSeries anchor'
]
cp['next_focus'] = 'Formalize the genuine least-missing-prime pointwise margin, test the new local TypeI correction and all small-core capacities without duplication. Gamma/TypeII and global OR incidence remain unestimated.'
cp['last_progress'] += ' Root16 full-read FINAL1 T1-T8 and provisional A1-A10. Selected13.8/14.1; authorized two genuinely new complete banks, no results presumed. Dispatched formalizer3 actual product/tail/Euler-harmonic margin; formalizer4 pending role2 FINAL slot. Primary BMOR pi_AP3 Theorem1.3 verified at arxiv1802.00085, constants1/840 and8e9, never applied to finiteN1e8. No16 Lean compilation or victory yet.'
cp['previous_goal_turn_classification'] = 'progress'
for item in ['round16/agent1_bilinear_covariance.md', 'round16/agent2_or_incidence.md', '.arbor/sessions/parity/.coordinator/messages/round16_selection.md', '.arbor/sessions/parity/experiments/13.8/executor_prompt.md', '.arbor/sessions/parity/experiments/14.1/executor_prompt.md']:
    if item not in cp['previous_goal_turn_evidence']:
        cp['previous_goal_turn_evidence'].append(item)
checkpoint_path.write_text(json.dumps(cp, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print('ROUND16_SELECTION_RECORDED; no arithmetic or Lean executable invoked.')
