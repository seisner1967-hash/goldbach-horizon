"""Metadata text generator only; never import/execute old tools or Lean."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
OLD = JUDGE / "batch14"


def put(name, text):
    with (OWN / name).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


builder = (OLD / "prepare_metadata.py").read_text(encoding="utf-8").replace("batch14", "batch15").replace("BATCH14", "BATCH15")
builder = builder.replace('"role3/discrete_circle_source22/revision02", "7ee2abb27d959f1511abb59e8425578b420d3e972a8d03eaff26635ac8fd581c"',
    '"role3/discrete_circle_source22/revision03", "f24c702b0a6cd71e88ae1279061a45e02fa04f12f8e8641444d3b5e1803e8f02"')
builder = builder.replace('"SOURCE_REVISION_NOT_COMPILED", "391197"', '"SOURCE_REVISION03_NOT_COMPILED", "2ceb49"')
start = builder.index("    support = [")
end = builder.index("    for path, digest, chunk in support:", start)
support = '''    support = [
        (JUDGE / "discrete_source_review_revision03.md", "3bf2fad41ff05861baaff4566cd19fae21f8dd073a28c6aeb00d62265a151647", "aa37c7"),
        (JUDGE / "discrete_source_review_revision02.md", "bee48a1fdb3347206ede5998f412e4aeebfe26cde334163d7220a887c364c459", "76fdfa"),
        (BASE / "round22/role3/discrete_circle_source22/revision03/source_review22.md", "9fd8d6e2d25dd3cfed25f01adae5b9e559b40b468b19899a0ba615879bfe6350", "f297aa"),
        (BASE / "round22/role3/discrete_circle_source22/revision03/read_receipts22.json", "fcb78f20e00329ffa2b4519a0516a7d8fd4cd347c23d2498af6dac5bb1adb7c2", "f297aa"),
        (BASE / "round22/role3/discrete_circle_source22/source_contract22.md", "f930ed4353729c73047a36d2ec68bab7387ee4ce2cdb2f4cf8ba1b13a941c49c", "09932d"),
        (BASE / "round22/role3/discrete_circle_source22/read_receipts22.json", "866035a817c15b6d094a6d491bb49093cab69dc1e0fe6bcd5e3664c148ac94d8", "3241a7"),
        (JUDGE / "batch14/adjudication.md", "c4538d181f80e2b9b7a89d546bdd0a8a59a9a2de163a9da287280d3972499327", "f2d196"),
        (JUDGE / "batch14/completion_receipt.json", "ac2d9b446664327e79d069c8015ec6f9f7990a3d1129dc5fa3d5bf91ec4784df", "f2d196"),
        (JUDGE / "batch14/batch14_attempt01/receipt.json", "ae9796da1bc74630389a1a547c8cb5bb2fbfda16b6295e41d8becea46855c45d", "bc32b7"),
        (JUDGE / "batch14/batch14_attempt01/DiscreteThermalProjection22.log", "879f2978a6de8935608661b3194a36c728fbff743c864c3f114405fc463c3d0a", "8a6633"),
        (JUDGE / "batch14/batch14_attempt01/DiscreteThermalProjection22_FIN.json", "1ef1a87c885aafa907c810a4a17f973923ea17755a5b4748c616616ccfc84104", "bc32b7")]
'''
builder = builder[:start] + support + builder[end:]
put("prepare_metadata.py", builder)
put("run_once.py", (OLD / "run_once.py").read_text(encoding="utf-8").replace("batch14", "batch15").replace("BATCH14", "BATCH15"))
source = BASE / "round22/role3/discrete_circle_source22/revision03/DiscreteThermalProjection22.lean"
(OWN / "sources").mkdir(exist_ok=False)
with (OWN / "sources/DiscreteThermalProjection22.lean").open("xb") as stream:
    stream.write(source.read_bytes())
put("preparation.md", '''# Lot15 indépendant — SOURCE03 du discret29

ROLE5, scope unique DiscreteThermalProjection22 revision03 SHAf24c702b0a6cd71e88ae1279061a45e02fa04f12f8e8641444d3b5e1803e8f02. Un module29=20theoremes9definitions29prints qualifies ; aucune dependance locale ou olean auteur. Baseline ROOT14 observee75/1223,18PASS8FAIL ; hypothese76/1252 seulement apres vrai PASS et observation ROOT. Tous anciens lots01-14 et3089archives restent clos, readonly et lies par leurs octets. Aucun ancien module recompile ni banc rejoue.

Revue mathematique independante : judge5/discrete_source_review_revision03.md SHA3bf2fad41ff05861baaff4566cd19fae21f8dd073a28c6aeb00d62265a151647 FULLaa37c7 ; sourceFULL2ceb49, docs auteurFULLf297aa. Quatre raccords techniques propres au vrai FAIL14 sont corriges sans changer aucun enonce/domaine : simp sous deux ite au lieu de rw dependent ; push_cast dans hc et but ; cast negatif final. Les29headers sont compares par metadata aux anciens enonces. Aucun deficit SOURCE detecte ne constitue encore un PASS Lean. Garde A0, divisibilites signees, caractere exp concret, somme geometrique, normalisationK/exp et vraies Lambda/puisances premieres sont construits. a reel quelconque pour polynome fini ; N<=M et max N(2M-N)<K paient l'antidiagonale et l'absence d'aliases. Aucune orthogonalite/cible/majoration finale supposee.

Outils neufs lus FULL avant execution metadata : create_tools_source.py lit uniquement le texte des outils14 et cree les nouveaux textes, jamais d'import ou execution ancienne. prepare_metadata.py ne lance aucun subprocess ; copie byte-exacte sous sources racine commune, comptes/prints/tokens et provenance verifies ; inventaire de tous anciens fichiersJuge et hashes des3089archives ; fermeture imports lexicale exhaustiveInit+Init.Prelude, sources et cacheoleans huitpackages. Ce traitement de fichiers n'est aucune elaboration, preuve ou evaluation mathematique. Aucun grand import/manifest n'est revendiqueFULL mathematique ; tous bytes plus projectionheader honnete. Creations exclusives seulement, aucun overwrite/retryfreeze.

run_once.py reste SOURCE non execute : gateROOT15 distincte lie manifest/launcher/preparedreceipt/runtimes ; tentativeunique batch15_attempt01, unchildLean au plus, timeout300s/maxHeartbeats1000000 ; cwd et sourcecommonroot batch15/sources. LEAN_PATH sortieexclusive neuve, readonly_oleans vide, huit caches packages existentes ; pas d'olean auteur ou ancien lot. PREEXEC hashes/captures/commandes/plan puis STARTglobalmodule, stdoutstderr integral, FIN/log/olean ; POSTEXEC conservation et receiptstandardstatus/modules_passed/declarations_passed/all_current_bytes_preserved. Premier FAIL ferme, aucun retry/probe/numérique.

Parser exact29noms dans ordre : propext/Classical.choice/Quot.sound seulement et emptyaxioms reel explicitement reconnu ; sorryAx/native_decide/Lean.ofReduceBool rejectes. SOURCE sorry/admit/axiom/unsafe/native_decide rejectes lexicalement hors commentaires. PASS exige exit0 nouvelolean couvertureexacte et conservationphysique ; avant invocation aucune declaration n'est acquise.

Pythonfixe4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c -B -X utf8 ; Lean4.15SHA8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08 ; mathlib9837ca9d65d9de6fad1ef4381750ca688774e608. Pas installation/git/banc/probe. AuxiliaireCIRCLE seulement, pas NTTprogramme effectivementpret ni coefficientN1e8 calcule, H1/globalC5/PP/frontiere/D_N/Goldbach/WIN. Mellin11 et NTT/PARAMETER_GUARD sont horslot15 et sans runtimeautorise.
''')
print("SOURCE_TOOLS_AND_EXACT_COPY_ONLY_CREATED")
