"""New batch16 metadata text tools only; no candidate import or compiler."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
OLD = JUDGE / "batch15"


def put(name, text):
    with (OWN / name).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


builder = (OLD / "prepare_metadata.py").read_text(encoding="utf-8").replace("batch15", "batch16").replace("BATCH15", "BATCH16")
start = builder.index("SPECS = ")
end = builder.index("\ndef sha(path):", start)
builder = builder[:start] + '''SPECS = (
    ("RationalLogQuantization22", "role3/log_quantization_source22/revision02", "9e59eb6b8aa4efcb5cc6cdc27d7d7a7d24517986fcd1ad2b4413b97c0efc1fb0", 23, 15, "SOURCE_ONLY_NOT_COMPILED", "87a11a", "GoldbachLogQuantization22"),
    ("QuantizedLambdaEnvelope22", "role3/log_quantization_source22/revision02", "526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331", 9, 5, "SOURCE_ONLY_NOT_COMPILED", "a87644", "GoldbachQuantizedCoefficient22"))
MODULES = tuple(row[0] for row in SPECS)
LOCAL_DEPENDENCIES = ()

''' + builder[end:]
builder = builder.replace("for module, folder, digest, nthm, ndef, status, chunk in SPECS:", "for module, folder, digest, nthm, ndef, status, chunk, namespace in SPECS:")
builder = builder.replace("NAMESPACE", "namespace")
builder = builder.replace("CONCRETE_FINITE_CHARACTER_ORTHOGONALITY_A0_CIRCLE_TRUE_LAMBDA_PP_AUX_ONLY", "CANONICAL_LOG32_TRUE_PRECISION_LAMBDA_PP_CONTINUOUS_COEFFICIENT_ENVELOPE_AUX_ONLY")
start = builder.index("    support = [")
end = builder.index("    for path, digest, chunk in support:", start)
builder = builder[:start] + '''    support = [
        (JUDGE / "log_quantization_source_review_revision02.md", "a8b74e2d2132ad40f0caa44e49ebd14cca234993bd0fd26f30ad83f15c5fcb65", "2bccd7"),
        (BASE / "round22/role3/log_quantization_source22/revision02/dependency_contract22.md", "cdb1b8510c13fe6ff69b6ed510df90335a831cef0181182c050c1781965fe91f", "587fd9"),
        (BASE / "round22/role3/log_quantization_source22/revision02/source_manifest22.json", "3d0af8eefbb29fd902bf3b1b86b4b15bce7280cbb262b1159486165ae2fd6a74", "587fd9"),
        (BASE / "round22/role3/log_quantization_source22/revision02/read_receipts22.json", "de4b33633a9e66471ed7a3d00c63dab2e522af6d356bc0968115076c3b29bcf9", "c127c0"),
        (JUDGE / "batch15/adjudication.md", "e2fda965a5cc1060a42920e5e889dc41f1867a2a6f091fb75ba132b7baaf1f49", "1b4643"),
        (JUDGE / "batch15/completion_receipt.json", "221d5c034dc90424deca0b566b1003e104b32453294ff8a305a7578b9eb71d3d", "1b4643"),
        (JUDGE / "batch15/batch15_attempt01/receipt.json", "ee18a68ce36db7757a139a803a7c555fb33dc9f99820cc1e3cf7b15222049845", "652cc7"),
        (JUDGE / "batch15/batch15_attempt01/DiscreteThermalProjection22.log", "5a99f3e74a991301a707747540267ab38d0ea673b9ac5a53aed5f38359a1f0da", "652cc7")]
''' + builder[end:]
start = builder.index("    api_reads = [")
end = builder.index("    old_rows = ", start)
builder = builder[:start] + '''    api_reads = [
        ("Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean", "054dec", "TARGETED_272_299"),
        ("Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean", "054dec", "TARGETED_197_234"),
        ("Mathlib/Topology/Algebra/InfiniteSum/Order.lean", "054dec", "TARGETED_30_61"),
        ("Mathlib/Data/Nat/Log.lean", "054dec/b3b8e6", "TARGETED_208_234_106_150"),
        ("Mathlib/Analysis/SpecificLimits/Basic.lean", "b3b8e6", "TARGETED_278_300"),
        ("Mathlib/NumberTheory/VonMangoldt.lean", "b3b8e6", "TARGETED_58_86"),
        ("Mathlib/Data/Nat/Prime/Defs.lean", "b3b8e6", "TARGETED_254_284"),
        ("Mathlib/Algebra/Order/Floor.lean", "b3b8e6", "TARGETED_642_680")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
    old_sources = (("RationalLogQuantization22", "d7ea4d46f0c595c05ccb140ee310996e3c257a240bde29a58c6a7c7811bce396"),
        ("QuantizedLambdaEnvelope22", "428836508d2edfe22c4639101f0b7a99ff34dbf57ea9375b72ab509e410ec1a3"))
    def headers(path):
        text = lean_code(path)
        return [" ".join(text[hit.start():text.index(":=", hit.end())].split())
            for hit in re.finditer(r"^(?:def|theorem)\\s+\\w+", text, re.M)]
    for module, expected in old_sources:
        original_old = BASE / "round22/role3/log_quantization_source22" / (module + ".lean")
        if sha(original_old) != expected: raise RuntimeError("Old source changed")
        if headers(original_old) != headers(OWN / "sources" / (module + ".lean")):
            raise RuntimeError("Source contract headers changed")
        bindings[str(original_old)] = expected
        reads.append((original_old, "BYTE_HASH_AND_LEXICAL_HEADERS_ONLY_NOT_FULL", "CURRENT_METADATA"))
''' + builder[end:]
builder = builder.replace('"truncated_reads_excluded": [], "corrected_read_path_error": "85133f Analysis/Complex/Exponential.lean missing; corrected745178/7d0bb6",',
    '"truncated_reads_excluded": ["ae4a74"], "empty_API_output_not_counted_as_read": "e7369c corrected054dec",')
builder = builder.replace('"module_count": 1, "total_declarations": 29, "theorem_count": 20, "definition_count": 9,', '"module_count": 2, "total_declarations": 52, "theorem_count": 32, "definition_count": 20,')
builder = builder.replace('"previous_official_modules": 75, "previous_official_declarations": 1223,', '"previous_official_modules": 76, "previous_official_declarations": 1252,')
builder = builder.replace('"hypothetical_after_all_PASS_modules": 76, "hypothetical_after_all_PASS_declarations": 1252,', '"hypothetical_after_all_PASS_modules": 78, "hypothetical_after_all_PASS_declarations": 1304,')
builder = builder.replace('"modules": 1, "declarations": 29, "theorems": 20, "definitions": 9,', '"modules": 2, "declarations": 52, "theorems": 32, "definitions": 20,')
builder = builder.replace('"one_module_SOURCE_not_elaborated": True', '"two_modules_SOURCE_not_elaborated": True')
put("prepare_metadata.py", builder)
launcher = (OLD / "run_once.py").read_text(encoding="utf-8").replace("batch15", "batch16").replace("BATCH15", "BATCH16")
launcher = launcher.replace("one finite discrete projection auxiliary", "two canonical-log and coefficient auxiliaries")
launcher = launcher.replace('MODULES = ("DiscreteThermalProjection22",)', 'MODULES = ("RationalLogQuantization22", "QuantizedLambdaEnvelope22")')
launcher = launcher.replace('"compiler_invocations_maximum": 1', '"compiler_invocations_maximum": 2')
launcher = launcher.replace('"gate_sha256": gate_sha, "child_invocations_maximum": 1, "hidden_retries": False})\n    rows = []',
    '"gate_sha256": gate_sha, "child_invocations_maximum": 2, "hidden_retries": False})\n    rows = []')
put("run_once.py", launcher)
(OWN / "sources").mkdir(exist_ok=False)
for module in ("RationalLogQuantization22", "QuantizedLambdaEnvelope22"):
    source = BASE / "round22/role3/log_quantization_source22/revision02" / (module + ".lean")
    with (OWN / "sources" / (module + ".lean")).open("xb") as stream:
        stream.write(source.read_bytes())
put("preparation.md", '''# Lot 16 indépendant — préparation SOURCE52 uniquement

Sélection ROOT : RationalLogQuantization22 révision02 (38=23thm15defs,9e59eb6b…) puis QuantizedLambdaEnvelope22 révision02 (14=9thm5defs,526354f4…). Deux modules52=32theoremes20definitions52prints, namespaces exacts distincts ; aucune dépendance locale ancienne ou olean auteur. Baseline ROOT observée après15 :76modules1252aux ; proposition78/1304 seulement si deux vrais PASS et observation ROOT. Tous lots01–15 sont clos readonly,3089archives préservées. Revue SOURCE indépendante a8b74e2d… FULL2bccd7, sources FULL87a11a/a87644, contrat et manifeste FULL587fd9, lectures FULLc127c0. Aucun PASS auteur, aucune compilation/probe/numérique de ces sources.

Le vrai HasSum logarithmique et le majorant géométrique ferment R32=9/(4*65*3^65). Nat.log2/les domaines2<=p<=1e8 donnent z dans[0,1/3] et width<=1/S. NearestEven rationnel tie-to-even puis clamp[0,32S] paient |logp−A32/S|<=1/S ; aucune précision/epsilon fournie en prémisse. Vraie Lambda IsPrimePow/minFac avec toutesPP, bornes32 construites, produit64/S, somme finie et normalisation par S² donnent E(N,S)=(N+1)(64/S+1/S²). E continu sur s>0 ; les conclusions de précision concernent uniquement S=2^58 fixé et N<=1e8. Aucun coefficient cible/minoration finale supposé. Les32thm ne paient ni réalisation native/commonD/divmod/carries/catalogue, ni NTT/CRT/coeffN calculé, H1global/PPfrontiere/D_N/WIN.

Nouveaux outils metadata seulement, lus FULL avant appel : générateur lit les outils15 comme texte, jamais import ou ancien exécutable. Builder vérifie copies byte-exactes,52headers identiques aux versions anciennes préservées par hash/lexical seulement, counts/noms/prints/tokens interdits, racine unique sources pour les deux modules. Imports source+cacheolean et Init/Prelude fermés exhaustivement depuis huitpackages/mathlib9837ca9d ; import local Rational est exclu des caches et doit provenir de la première compilation neuve. Manifestes hachés tousbytes avec headerprojection honnête, pasrawFULL de grands imports ; créations exclusives/nooverwrite/no freeze retry. Les textes et registres ne sont aucune évaluation mathématique ou preuve Lean.

Launcher SOURCE non exécuté avant gate ROOT16 spécifique : unique batch16_attempt01, au plus2children séquentiels, premierFAIL ferme et second NON_INVOKED. Chaque enfant timeout300s et maxHeartbeats1000000 ; même cwd et commonroot batch16/sources ; LEAN_PATH sortie neuve puis readonly_oleans vide puis huit caches. Le premier nouvelolean sert exclusivement à l'import du second ; aucun olean auteur/ancienmodule. PRE/STARTglobalmodule/commands/captures/logstdoutstderr/FIN/olean/POST/receipt réels conservés. Parser52prints compare noms/ordre exacts et axiomes standardpropext/Classical.choice/Quot.sound ; véritables emptyaxioms acceptés/listés, missingprints et sorryAx/native_decide/ofReduceBool refusés. Source sorry/admit/axiom/unsafe/native_decide refusés horscomments. PASS seulementexit0+olean+couverture+conservation ; aucun crédit partiel officiel avant observerROOT.

Python fixé -B -X utf8 SHA4278cf2a296f31737cae77cafeeb3dc71683094cf3b8fd6f3f02c968687e771c ; Lean4.15.0 SHA8a1ef18583d74d917194bba4743ce9765bad64b00c52bada002ee44796fb9e08. Aucun runtime nouveau, installation/git/oldcompile/banc/probe/retry. SOURCE native DIT/DIF est un audit séparé horslot16 et sans build/import/exécution autorisés.
''')
print("NEW_BATCH16_SOURCE_TOOLS_EXACT_TWO_COPIES_CREATED_ONLY")
