"""Fresh batch19 metadata text generation only. No candidate imports or compiler."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
PRIOR = JUDGE / "batch18"


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError("Template not unique: " + old[:80])
    return text.replace(old, new, 1)


def write_new(path, text):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


builder = (PRIOR / "prepare_metadata.py").read_text(encoding="utf-8")
builder = builder.replace("batch18", "batch19").replace("BATCH18", "BATCH19")
start, end = builder.index("SPECS = ("), builder.index("\n\n\ndef sha")
builder = builder[:start] + '''SPECS = (
    ("FiniteFieldProjection22", "role3/finite_field_projection_source22", "2b1cc267ce780a6a45c039f4b4b82d5a4ad4541fa224d76413dec5432658a48a", 20, 4, "SOURCE_ONLY_NOT_COMPILED", "8a0959", "GoldbachFiniteFieldProjection22"),)
MODULES = tuple(row[0] for row in SPECS)
LOCAL_DEPENDENCIES = ("QuantizedLambdaEnvelope22", "RationalLogQuantization22")
DEP_RECEIPT = JUDGE / "batch17/batch17_attempt01/receipt.json"
DEP_RECEIPT_SHA = "9449666ee8bdbbae74ea849e5a9ce2eb5c0c5bd7dd24c14a2d28065068178298"
DEP_SPECS = (
    ("QuantizedLambdaEnvelope22", "526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331", "e821070b97b3fa4b71a3e279ecb9bc6c0de6cafdfe9dc8712b5d5a22858a6485", 14, "0445ad"),
    ("RationalLogQuantization22", "dfabcabf39ecc1ba7769eb99ea73e0483dc6925f0bb3d11c05891d22c0a787a7", "20db07cdfb5717d7f9ab0b3e75d3c15b9e16c6820ad5285bd7debb62b0a31434", 38, "f4d314_HISTORICAL_FULL"),)
''' + builder[end:]
builder = replace_once(builder,
    '    if module == "GammaPrerequisites22":\n        return DEP_SOURCE, OWN / "readonly_oleans/GammaPrerequisites22.olean"',
    '''    if module in LOCAL_DEPENDENCIES:
        return JUDGE / "batch17/sources" / (module + ".lean"), OWN / "readonly_oleans" / (module + ".olean")''')
builder = builder.replace("REAL_GAMMA_SCALAR_MELLIN_INVERSION_X_POSITIVE_AUX_ONLY", "FINITE_FIELD_EXACT_SIGNED_CHARACTER_PROJECTION_CANONICAL_A32_AUX_ONLY")
start, end = builder.index('    depdir = OWN / "readonly_oleans"'), builder.index('    old_rows = ')
builder = builder[:start] + '''    depdir = OWN / "readonly_oleans"; depdir.mkdir(exist_ok=False)
    if sha(DEP_RECEIPT) != DEP_RECEIPT_SHA:
        raise RuntimeError("Independent batch17 receipt changed")
    dep_receipt = json.loads(DEP_RECEIPT.read_text(encoding="utf-8"))
    if (dep_receipt["status"] != "INDEPENDENT_BATCH17_AUX_PASS"
            or not dep_receipt["all_inputs_unchanged"]
            or dep_receipt["modules_passed"] != 2 or dep_receipt["declarations_passed"] != 52):
        raise RuntimeError("Independent batch17 provenance invalid")
    deps = []
    for module, source_digest, olean_digest, count, chunk in DEP_SPECS:
        source = JUDGE / "batch17/sources" / (module + ".lean")
        obj = DEP_RECEIPT.parent / (module + ".olean")
        log = DEP_RECEIPT.parent / (module + ".log")
        fin = DEP_RECEIPT.parent / (module + "_FIN.json")
        row = next(row for row in dep_receipt["rows"] if row["module"] == module)
        if (sha(source) != source_digest or sha(obj) != olean_digest
                or row["source_sha256"] != source_digest or row["olean_sha256"] != olean_digest
                or row["status"] != "INDEPENDENT_LEAN_AUX_PASS" or row["exit_code"] != 0
                or not row["exact_axiom_coverage_standard_only"] or len(row["axiom_rows"]) != count
                or sha(log) != row["log_sha256"] or json.loads(fin.read_text(encoding="utf-8")) != row):
            raise RuntimeError("Independent dependency PASS invalid: " + module)
        copy = depdir / (module + ".olean")
        with copy.open("xb") as stream: stream.write(obj.read_bytes())
        if sha(copy) != olean_digest: raise RuntimeError("Readonly dependency copy mismatch")
        deps.append({"module": module, "source": str(source), "source_sha256": source_digest,
            "olean_original": str(obj), "olean_copy": str(copy), "olean_sha256": olean_digest,
            "independent_receipt": str(DEP_RECEIPT), "independent_receipt_sha256": DEP_RECEIPT_SHA,
            "status": "INDEPENDENT_LEAN_AUX_PASS", "recompile_authorized": False})
        for path in (source, obj, copy, DEP_RECEIPT, fin, log): bindings[str(path)] = sha(path)
        reads.append((source, "FULL_READONLY_INDEPENDENT_SOURCE", chunk))
    reads.append((DEP_RECEIPT, "FULL_PREVIOUS_CLOSED_INDEPENDENT_RECEIPT", "ee2407_HISTORICAL_FULL"))
    support = [
        (JUDGE / "finite_field_projection_source_review22.md", "336e7e5a727d42a8de650186619ba2995dad23e63d0edcace73cd33ae8170917", "785fae"),
        (BASE / "round22/role3/finite_field_projection_source22/source_contract22.txt", "8e9797c1628762c82de4e333c326034f893d839e320f779b4576e7910ea4ca0d", "229926"),
        (BASE / "round22/role3/finite_field_projection_source22/source_read_receipts22.json", "71d97c57c71de01226e0d251fd60b7ecdeefe3a5b65f543b61f3102e2aa6a4d8", "229926"),
        (JUDGE / "batch17/adjudication.md", "ffab547e870266510c64ebe011b89998fe1d218ec27f347f8ca8a3ce38a331e3", "602acc_HISTORICAL_FULL"),
        (JUDGE / "batch17/completion_receipt.json", "150b360cfb3fabbcc3a1a42456c2a1ebd338683af9863c68134310c06775cdaa", "602acc_HISTORICAL_FULL"),
        (DEP_RECEIPT, DEP_RECEIPT_SHA, "ee2407_HISTORICAL_FULL"),
        (JUDGE / "batch18/adjudication.md", "e00bfdcb0b871103c295b73104a4e0feef770cedbb4e6d64758ff97f7417339a", "f84a7b"),
        (JUDGE / "batch18/completion_receipt.json", "28896f689441f63c3cf3d8bd8c683ecb3d989d5650ce8aa49d2e858b5d072b10", "f84a7b")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean", "990f82", "TARGETED_45_79_278_329_386_440"),
        ("Mathlib/Algebra/GeomSum.lean", "990f82", "TARGETED_225_247"),
        ("Mathlib/Algebra/BigOperators/Ring.lean", "990f82", "TARGETED_31_66"),
        ("Mathlib/Data/Finset/NatAntidiagonal.lean", "990f82", "TARGETED_1_60"),
        ("Mathlib/Algebra/GroupWithZero/Basic.lean", "990f82", "TARGETED_399_439"),
        ("Mathlib/Data/ZMod/Basic.lean", "0445ad", "TARGETED_451_482_564_588_1315_1346")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
''' + builder[end:]
builder = builder.replace('"total_declarations": 11, "theorem_count": 9, "definition_count": 2', '"total_declarations": 24, "theorem_count": 20, "definition_count": 4')
builder = builder.replace('"hypothetical_after_all_PASS_declarations": 1315', '"hypothetical_after_all_PASS_declarations": 1328')
builder = builder.replace('"declarations": 11, "theorems": 9, "definitions": 2', '"declarations": 24, "theorems": 20, "definitions": 4')
builder = builder.replace('"readonly_independent_dependency_count": 1', '"readonly_independent_dependency_count": 2')
builder = builder.replace('"truncated_reads_excluded": ["f01eb1", "a732a6", "56545d", "2d8015", "3b6479"]', '"truncated_reads_excluded": ["f01eb1", "a732a6", "56545d", "2d8015", "3b6479", "196191_combined_overall_truncated"]')
write_new(OWN / "prepare_metadata.py", builder)

launcher = (PRIOR / "run_once.py").read_text(encoding="utf-8")
launcher = launcher.replace("batch18", "batch19").replace("BATCH18", "BATCH19")
launcher = launcher.replace("ThermalGammaMellinInverse22", "FiniteFieldProjection22")
launcher = launcher.replace('LOCAL_DEPENDENCIES = ("GammaPrerequisites22",)', 'LOCAL_DEPENDENCIES = ("QuantizedLambdaEnvelope22", "RationalLogQuantization22")')
launcher = launcher.replace("one genuine Gamma scalar Mellin inversion auxiliary", "one exact finite-field character projection auxiliary")
write_new(OWN / "run_once.py", launcher)

write_new(OWN / "preparation.md", '''# Lot19 : préparation indépendante SOURCE seulement

ROLE5, sélection ROOT explicite après clôture18 observée3343a3/session74910→f11553 exit0. Baseline officielle78 modules/1304 déclarations incluant les définitions. Cible unique FiniteFieldProjection22 source2b1cc267ce780a6a45c039f4b4b82d5a4ad4541fa224d76413dec5432658a48a,24 déclarations=20 théorèmes+4 définitions,24 prints qualifiés exacts. Aucune compilation auteur ou indépendante de ce module encore acquise.

Revue mathématique indépendante close finite_field_projection_source_review22.md SHA336e7e5a727d42a8de650186619ba2995dad23e63d0edcace73cd33ae8170917 FULL785fae. Chaîne cohérente en SOURCE : somme géométrique signée avec tous les alias, garde max(N,2M−N)<K, caractéristique (K:F)≠0, rectangle filtré puis antidiagonale pour N≤M, normalisation inverse, expression DFT exacte, vrai integerLambda canonique et toutes puissances premières. Les racines/primalités concrètes des cinq moduli ne sont pas prouvées ici ; Fact p.Prime et IsPrimitiveRoot ω K sont des hypothèses de domaine explicites, jamais une égalité finale ou cible supposée. Les casts, instances et tactiques exactes restent à compiler.

Deux seules dépendances locales : QuantizedLambdaEnvelope22 source526354f4b96006eb2b297477fb6f09dd8a683e88cc95feb816a31357df0a2331 / olean indépendant PASS17 e821070b97b3fa4b71a3e279ecb9bc6c0de6cafdfe9dc8712b5d5a22858a6485 ; son import transitif RationalLogQuantization22 source dfabcabf39ecc1ba7769eb99ea73e0483dc6925f0bb3d11c05891d22c0a787a7 / olean20db07cdfb5717d7f9ab0b3e75d3c15b9e16c6820ad5285bd7debb62b0a31434. Reçu indépendant17 SHA9449666ee8bdbbae74ea849e5a9ce2eb5c0c5bd7dd24c14a2d28065068178298, deux vrais PASS/52 prints standard, clampInteger sans axiomes. Le builder vérifie sources, oleans, logs, FIN et reçu avant copie exacte dans readonly_oleans ; ces modules ne seront pas recompilés. Gamma n'est ni importé ni proposé dans ce lot.

La copie exacte du seul nouveau module est sous batch19/sources, racine unique correspondant au futur cwd Lean. Le builder metadata lexical ne parse ni n'élabore Lean : il lie explicitement Init/Prelude et ferme récursivement chaque import avec vraies sources et vrais oleans cache, huit packages readonly et runtime Lean4.15/mathlib9837ca9d ; tout import manquant garde la préparation ouverte. Seuls les deux oleans indépendants17 et les caches seront ajoutés au futur LEAN_PATH avec le dossier de sortie neuf ; aucun olean auteur.

Outils neufs dérivés textuellement des templates18 sans les importer/exécuter. Lire FULL le générateur puis le builder, le launcher, cette note et la copie de source avant unique préparation. Inventaire hash de tous les anciens fichiers Juge hors lot19, protection des3089 archives et provenance17/18 intégrés. Un manifeste volumineux sera lu comme projection explicite des en-têtes et vérification de tous octets ; il ne recevra pas une fausse qualification FULL texte. Catalogue/reçus/outils et audit seront lus FULL sans troncature.

Le launcher exige une nouvelle gate ROOT spécifique ROUND22_JUDGE5_BATCH19_AUTHORIZATION liée aux neuf objets gelés, au runtime fixé et aux deux seules dépendances. Tentative unique batch19_attempt01 : un seul enfant Lean, timeout300s, sortie olean indépendante, aucun retry/probe/installation/ancien compile/numeric. Toute START existante ou sortie existante interdit de relancer. PREEXEC capte sources, outils, catalogue, manifeste, reçu, gate et supports avec hashes ; START et FIN globals et module, log fusionné stdout/stderr, POSTEXEC et reçu réels. Le parseur accepte les listes d'axiomes vides véritables, vérifie les24 noms exacts et n'autorise que propext, Classical.choice, Quot.sound ; recovery sorryAx et tout autre axiome refusent le PASS. Ce paquet ne préjuge pas combien de ces déclarations auront une liste vide.

Au FIN futur : lecture FULL log/reçu, exactitude couverture24, nouvelle adjudication/completion au format status réel, modules_passed/declarations_passed/all_current_bytes_preserved, rehash inputs/archives/anciens lots/captures ; crédit uniquement après observation ROOT. Tout FAIL sera décrit selon sa cause réelle, sans le rebaptiser obstruction de parité. Hypothétique PASS79/1328 seulement, aucune modification actuelle78/1304.

Portée : projection spectrale finie compatible avec l'axe de corrélation autorisé, jamais une nouvelle forme bilinéaire de théorie des nombres. Contrat exact finitement calculable distinct de code natif prêt et banc coefficientN terminé. Primalités/racines des cinq moduli, butterflies, catalogue, mots/GMP, DIT/DIF, CRT et transport des sorties restent ouverts ; H1/globalM/C5, correctionPP/frontière, D_N et WIN restent ouverts. Aucun lot20 ou build/nouveau banc autorisé par cette préparation.
''')

source_dir = OWN / "sources"
source_dir.mkdir(exist_ok=False)
original = BASE / "round22/role3/finite_field_projection_source22/FiniteFieldProjection22.lean"
with (source_dir / original.name).open("xb") as stream:
    stream.write(original.read_bytes())
print("Fresh metadata tools and exact SOURCE copy written; no builder or compiler invoked")
