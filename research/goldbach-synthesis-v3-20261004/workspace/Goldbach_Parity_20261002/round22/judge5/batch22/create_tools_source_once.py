"""File preparation only: new batch22 tools and exact author-source copies. No candidate import or compiler."""
from pathlib import Path
import hashlib

OWN = Path(__file__).resolve().parent
BASE = OWN.parents[2]
OLD = BASE / "round22/role4/concrete_ntt_roots_prepare21"
SRC = BASE / "round22/role4/roots_revision02"

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def put(name, text):
    with (OWN / name).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)

def replace_one(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError("EXACT_REPLACEMENT_COUNT:" + old[:70])
    return text.replace(old, new, 1)

def main():
    if any((OWN / name).exists() for name in ("prepare_metadata.py", "run_once.py", "sources", "prepared_manifest.json")):
        raise RuntimeError("NEW_TOOLS_ALREADY_EXIST")
    if sha(OLD / "prepare_metadata.py") != "16e79b156ecacf6cbcc2ec659a9366d6bcb34e8622a319a689e15fabf6a8ce38" or sha(OLD / "run_once.py") != "9304c826f280d0c4c092e3854ef55c1ede63529488de1065e3eeb71c8cfd9c76":
        raise RuntimeError("READONLY_TEMPLATE_CHANGED")
    builder = (OLD / "prepare_metadata.py").read_text(encoding="utf-8").replace("Batch21", "Batch22").replace("BATCH21", "BATCH22")
    builder = replace_one(builder, 'SOURCE_DIR = BASE / "round22/role3/concrete_ntt_roots_source22"', 'SOURCE_DIR = BASE / "round22/role4/roots_revision02"')
    builder = replace_one(builder, 'REVIEW_DIR = BASE / "round22/role4/concrete_ntt_roots_review_source01"', 'REVIEW_DIR = SOURCE_DIR\nOLD21 = BASE / "round22/role4/concrete_ntt_roots_prepare21"')
    builder = builder.replace("433903d458f6ccd43f366e92265d0778250484f4721fcd885ca0a01a771e8e6a", "16c414a5d2f05c4ad273dde2245282aad452880b4d51df0aaed78f08d944b3bc")
    builder = builder.replace('"9a1c58"', '"197629"').replace('"958225"', '"03f3e5"')
    start, end = builder.index("SUPPORT = ("), builder.index("\n\ndef sha(")
    support = '''SUPPORT = (
    (SOURCE_DIR / "source_contract22.md", "08f08208cf959b3e92074b3ed95e7ae921114a1baf6b7ef5f7dd76784d570bcc", "FULL", "03f3e5"),
    (SOURCE_DIR / "source_catalog22.json", "aebeddfef2cf0ada938394c3478efbff937dd2f76ee283fbd794b080078bf489", "FULL", "31cebb"),
    (SOURCE_DIR / "source_read_receipts22.json", "4051672be3f6635da7444f13f161ab20e2d0c2b9a7da4b8a8f91b228268353ea", "FULL", "31cebb"),
    (SOURCE_DIR / "source_handoff22.json", "715032a2cbdd0d120e9d5c5b20145bf78b145b9ad2cec6fb14be969ad18be407", "FULL", "03f3e5"),
    (JUDGE / "concrete_ntt_roots_revision02_source_review22.md", "44be9f19fcbee716f62151d3c2b6c7787286dd3898f858aaf0b92fa2dc57acf8", "FULL", "949af5"),
    (OLD21 / "adjudication.md", "72d6b2759286cea9414431f87db7286522c42513fd3c316a50ed471cfaa322a1", "FULL", "ca8a19"),
    (OLD21 / "completion_receipt.json", "a157d392c19448f253e3781e26cf56e30de878a5995c40bf170b3d68a3af3898", "FULL", "ca8a19"),
    (OLD21 / "batch21_attempt01/receipt.json", "5ac9e5c7955ddacd7c486598dfe2e1bb011f116b48f04861cd75e73e20279964", "FULL", "f900fb"),
    (BASE / ".arbor/sessions/parity/.coordinator/messages/round22_judge_batch21_closed_observation.json", "6135ff4d335d29f6dba3745577063bd0aeb15400eda022132814e99da7e9bcd3", "FULL", "bda5bf"))
'''
    builder = builder[:start] + support + builder[end:]
    builder = builder.replace('observation["status"] != "INDEPENDENT_BATCH20_AUX_PASS"', 'observation["status"] != "INDEPENDENT_BATCH21_FAILED"')
    builder = builder.replace("Actual ROOT baseline20 observation mismatch", "Actual ROOT unchanged baseline after FAIL21 mismatch")
    builder = builder.replace('REVIEW_DIR / "review_receipts22.json"', 'REVIEW_DIR / "source_read_receipts22.json"')
    builder = builder.replace('item["scope"], item["receipt"]', '"HASH_PLUS_AUTHOR_RECORDED_" + item["read_scope"], item["tool_receipt"]')
    builder = replace_one(builder,
        '    old_rows = [{"path": str(path), "sha256": sha(path), "bytes": path.stat().st_size}\n                for path in sorted(JUDGE.rglob("*")) if path.is_file()]',
        '    old_paths = {path for path in JUDGE.rglob("*") if path.is_file() and not path.resolve().is_relative_to(OWN.resolve())}\n    old_paths.update(path for path in OLD21.rglob("*") if path.is_file())\n    old_rows = [{"path": str(path), "sha256": sha(path), "bytes": path.stat().st_size}\n                for path in sorted(old_paths)]')
    builder = builder.replace("BYTE_HASH_ALL_CLOSED_JUDGE_FILES_PRESENT_THROUGH_BATCH20", "BYTE_HASH_ALL_PRIOR_JUDGE_FILES_AND_EXPLICIT_ROLE4_CLOSED_BATCH21")
    builder = builder.replace('"author_provenance_capture_paths": []', '"author_provenance_capture_paths": [str(path) for path in sorted(OLD21.rglob("*")) if path.is_file()]')
    builder = builder.replace('"candidate_numeric_invocations": 0', '"candidate_numeric_invocations": 0, "numeric_invocations": 0')
    builder = builder.replace('"compiler_invocations": 0, "win": False', '"compiler_invocations": 0, "numeric_invocations": 0, "win": False')
    builder = builder.replace('"358bb1 recursive inventory truncated", "0c6104 broad API search truncated"', '"197629 missing source_contract22.txt excluded (Roots source itself FULL)", "0b8645 truncated API aggregate excluded"')
    launcher = (OLD / "run_once.py").read_text(encoding="utf-8").replace("batch21", "batch22").replace("BATCH21", "BATCH22")
    launcher = launcher.replace('"declarations_passed": sum', '"numeric_invocations": 0, "declarations_passed": sum')
    put("prepare_metadata.py", builder)
    put("run_once.py", launcher)
    put("preparation.md", """Lot22 SOURCE/PREPARE exclusivement, baseline officielle80/1339 après FAIL21.

Sources révision02 exactes de ROLE4 : Roots16c414… puis Bridgecefc071… ;2modules28=22thm6defs/28prints. Correction restreinte des16 sites val, SOURCE revue ROLE5 44be9f… ; aucun PASS auteur ni Lean/probe/math ici. Common root sources unique, copies exactes. L'olean Roots du futur essai peut alimenter Bridge uniquement après exit0 et audit axiomes exacts.

Trois dépendances readonly indépendantes : FiniteFieldProjection19 (030440…), Envelope17(e821…), Rational17(20db…). Sources/oleans/receipts/FIN/logs liés, aucune recompilation et aucun olean auteur. Imports transitifs cache4.15/mathlib9837ca9d et8packages, Init implicite de chaque nonprelude + Init.Prelude ; tous bytes source/olean/runtime vérifiés. Scope HEADER/HASH, aucune prétention FULL des milliers de preuves.

Tous fichiers Judge antérieurs sont inventoriés en excluant seulement ce lot22 neuf. Tous fichiers de la préparation/actual21 horsjudge5 sont ajoutés explicitement aux bindings clos et captures, avec son adjudication/completion/observation ROOT. Les19 bindings de l'auteur restent des scopes auteur recorded dans les receipts, pas des lectures FULL appropriées. 3089 archives sont physiquement rehashées. Grands JSON : projections des headers et traitement intégral des bytes/entrées, sans fauxRAWFULL.

Builder metadata unique après lectureFULL outils/audit/copies ; aucun subprocess ni calcul modulaire. Schéma standard inclut numeric_invocations=0. Cette préparation ne lance pas Lean. Nouvelle gate ROOT batch22 exacte indispensable : canonicalPY -I -S -B -X utf8,2children max Roots→Bridge,300s chacun,heartbeats1m,0retry/probe ; stopFIRSTFAIL, aucune compilation d'ancien module ni bank/native replay. PRE/START/FIN/logs/olean/POST/receipt, original/copie/gate toujours vérifiés. Parse exact de tous prints, y compris emptyaxioms si réellement affichés, standards propext/choice/Quot.sound seulement ; sorryAx/native_decide/ofReduceBool rejetés.

La compiler acceptance reste ouverte. Hypothétique82/1367 uniquement après2PASS entiers et observerROOT ; aucun coefficientN évalué, GMP/NTT/CRT, annulation globale, PP/frontière, D_N ou WIN payé. Aucun autre candidat n'entre dans22.
""")
    (OWN / "sources").mkdir(exist_ok=False)
    for module, digest in (("ConcreteNTTRoots22", "16c414a5d2f05c4ad273dde2245282aad452880b4d51df0aaed78f08d944b3bc"), ("ConcreteNTTA32Projection22", "cefc07197945f1e9710895d4a01455861ae6db21365cc44dec206178e76af4c3")):
        original = SRC / (module + ".lean")
        if sha(original) != digest:
            raise RuntimeError("SOURCE_CHANGED:" + module)
        with (OWN / "sources" / (module + ".lean")).open("xb") as stream:
            stream.write(original.read_bytes())
    print("NEW_BATCH22_TOOLS_AND_EXACT_SOURCE_COPIES_ONLY_NO_PREPARED_NO_LEAN")

if __name__ == "__main__":
    main()
