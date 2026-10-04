"""Fresh batch20 metadata text generation only; never import or run old tools."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
PRIOR = JUDGE / "batch18"


def replace_once(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError("Template block not unique: " + old[:80])
    return text.replace(old, new, 1)


def write_new(path, text):
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)


builder = (PRIOR / "prepare_metadata.py").read_text(encoding="utf-8")
builder = builder.replace("batch18", "batch20").replace("BATCH18", "BATCH20")
builder = builder.replace("role3/phase_mellin_inversion_source22", "role3/thermal_gamma_mellin_revision02")
builder = builder.replace("5271bbf9a9917a3ab61c6c7e0e747af4014e214b0867a9c81b43b5aa08fccec1", "daad8b5d5fb1181bfc714e1b470edd7d9a6ae07e9a1b76c384481964a42caf91")
builder = builder.replace('"2092de/a13eb7", "GoldbachThermalMellin22"', '"e7807e", "GoldbachThermalMellin22"')
start, end = builder.index('    support = ['), builder.index('    old_rows = ')
builder = builder[:start] + '''    support = [
        (JUDGE / "mellin_inverse_source_review_revision02.md", "8beb643b7f86fd8a70906f335468f4d9aed2eaf13748425a3eb79955a5a753b8", "d3100b"),
        (JUDGE / "mellin_inverse_source_review22.md", "ea23cf317cebdfaf4328f53f691fc9f22412550eabdff273cab94f373ed8d0a8", "2092de"),
        (BASE / "round22/role3/thermal_gamma_mellin_revision02/revision_contract22.txt", "ad20abd8b3ac65ad37d8c25f82e9891ac32fa9afa525b4493ac758d69e7bacd6", "618d04"),
        (BASE / "round22/role3/thermal_gamma_mellin_revision02/source_read_receipts22.json", "8aeabccdc49f835e1c6656f7fa0b02ac6d03be0f8c9b66a3e8ce8802e1a064bc", "618d04"),
        (JUDGE / "batch18/adjudication.md", "e00bfdcb0b871103c295b73104a4e0feef770cedbb4e6d64758ff97f7417339a", "f84a7b"),
        (JUDGE / "batch18/completion_receipt.json", "28896f689441f63c3cf3d8bd8c683ecb3d989d5650ce8aa49d2e858b5d072b10", "f84a7b"),
        (JUDGE / "batch18/batch18_attempt01/receipt.json", "5cafbee7186adfbc6a9459b26dfc077999a68bd5eef3758a391f805a49f4c84f", "d5301a"),
        (JUDGE / "batch19/adjudication.md", "af4bb865b233d921d895ca44b4dbfe265b3d6eac918ae311830c833ad860c5a1", "a318ab"),
        (JUDGE / "batch19/completion_receipt.json", "a9fc7f95a8115b9187c16e20a145a372c9a5bd80e07901ba4463ed505fa7da70", "a318ab"),
        (JUDGE / "batch19/batch19_attempt01/receipt.json", "1a645174f44f5545e6069139cd3d452f9eb6100f7946152c5cf50c56c8252d57", "0d4e79")]
    for path, digest, chunk in support:
        if sha(path) != digest: raise RuntimeError("Support provenance changed")
        bindings[str(path)] = digest; reads.append((path, "FULL_CURRENT_OR_PREVIOUS_CLOSED", chunk))
    api_reads = [
        ("Mathlib/Analysis/MellinInversion.lean", "a13eb7", "FULL_PREVIOUS_UNCHANGED_API"),
        ("Mathlib/Analysis/MellinTransform.lean", "2867e9_HISTORICAL", "TARGETED_35_96"),
        ("Mathlib/Analysis/SpecialFunctions/Gamma/Deriv.lean", "59a6a9_HISTORICAL", "TARGETED_35_44_75_85"),
        ("Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean", "59a6a9_HISTORICAL", "TARGETED_83_112_305_322"),
        ("Mathlib/MeasureTheory/Integral/IntegrableOn.lean", "59a6a9_HISTORICAL", "TARGETED_220_231_695_707"),
        ("Mathlib/Topology/Basic.lean", "dd195e", "TARGETED_1425_1459"),
        ("Mathlib/Order/Interval/Set/Defs.lean", "dd195e", "TARGETED_67_79"),
        ("Mathlib/MeasureTheory/Function/L1Space.lean", "dd195e", "TARGETED_427_446")]
    for relative, chunk, scope in api_reads:
        path = CACHE / "mathlib" / relative
        bindings[str(path)] = sha(path); reads.append((path, scope, chunk))
''' + builder[end:]
builder = builder.replace('"previous_official_modules": 78, "previous_official_declarations": 1304', '"previous_official_modules": 79, "previous_official_declarations": 1328')
builder = builder.replace('"hypothetical_after_all_PASS_modules": 79, "hypothetical_after_all_PASS_declarations": 1315', '"hypothetical_after_all_PASS_modules": 80, "hypothetical_after_all_PASS_declarations": 1339')
builder = builder.replace('"truncated_reads_excluded": ["f01eb1", "a732a6", "56545d", "2d8015", "3b6479"]', '"truncated_reads_excluded": ["f01eb1", "a732a6", "56545d", "2d8015", "3b6479", "196191_combined_overall_truncated"]')
write_new(OWN / "prepare_metadata.py", builder)

launcher = (PRIOR / "run_once.py").read_text(encoding="utf-8")
launcher = launcher.replace("batch18", "batch20").replace("BATCH18", "BATCH20")
write_new(OWN / "run_once.py", launcher)

write_new(OWN / "preparation.md", '''# Lot20 : Γ Mellin11 révision02, préparation SOURCE seulement

Sélection ROOT explicite après revue indépendante SHA8beb643b7f86fd8a70906f335468f4d9aed2eaf13748425a3eb79955a5a753b8 FULLd3100b et observation19 bdafba/session90132→4b4942 exit0. Baseline79 modules/1328 auxiliaires incluant les définitions. Lot neuf unique ThermalGammaMellinInverse22.lean source daad8b5d5fb1181bfc714e1b470edd7d9a6ae07e9a1b76c384481964a42caf91,11 déclarations=9 théorèmes+2 définitions et11prints, SOURCE non compilée.

Révision technique exacte : ContinuousAt.comp fixe f:ℝ→ℂ/g=Γ/x=t, Set.mem_Ioi.mp donne htpos, Function.comp_apply/gammaLine/abs normalisent mono'. APIs TARGETEDdd195e ; onze signatures/domaines/prints identiques lexicalement91c5f0. Aucun déficit SOURCE précis détecté ; le résultat de Lean, notamment les recovery aval, reste ouvert. L'ancienne source5271bb et le vraiFAIL18 restent immuables, zéro crédit18 et aucun replay.

L'identité conserve x>0, Re(s)=2 et le facteur1/(2π). Les preuves construisent convergence Mellin, continuité et vraie intégrabilité des deux demi-droites Γ(2±it), majorées par2exp(−πt/4), avant l'inversion réelle du cache MellinInversion. Aucune hypothèse d'inversion ou d'intégrabilité finale n'est donnée. Les objets réels sont Γ et exp(−x) ; échangeΛ/prolongement à un taux complexe sont des obligations séparées ouvertes.

Unique dépendance locale GammaPrerequisites22 indépendant PASS Juge02 : source9f5e5fe14d18e2b7c3ab364e461bfcc01d29ee4ef4af6d627d6ad9fcd102fbe7 / oleanfc0dad0b550f13a5c3a5b1e7cf1cfa22fc3a233822fc548cce155ab7a7274477 / reçua159b22e7ac4e8718f0572fdbf3e6d424294571eab01d5ed1ff979a821af48f9. Source/reçu/FIN/log exacts et23prints standards seront vérifiés avant copie byteidentique readonly ; aucune recompilation. Source neuve dans la racine commune batch20/sources, même futur cwd. Ni Envelope/FiniteField/racines concrètes, ni autres candidats SOURCE, ni BUILD04 n'entrent dans le lot.

Outils neufs générés textuellement depuis18, jamais importés/exécutés comme anciens outils. LectureFULL du générateur puis builder/launcher/note/copie source avant unique builder metadata. Ce builder ne lance aucun subprocess et ferme lexicalement Init/Prelude et tous imports sur sources/oleans réels des8packages readonly et runtime Lean4.15/mathlib9837ca9d. Aucun olean auteur sur futur LEAN_PATH. Inventaire bytehash de tous fichiers anciens Juge hors20 et3089archives protégées, captures futures des pièces, dépendance et supports18/19. Gros manifeste/imports/inventaire : projection honnête des en-têtes plus tous octets, pas rawFULL prétendu ; outils/catalogue/reads/reçu seront lusFULL.

Le launcher exige gateROOT20 nouvelle liée à manifeste/launcher/reçu préparé/runtime/uniqueGamma readonly, et vérifie la racine commune. Tentative unique batch20_attempt01,1child300s,0retry/probe/anciencompile/numérique/install/git. Préflight bindings+archives ; copies PREEXEC, START/FIN globaux et module, log fusionné stdout/stderr, olean indépendant, POSTEXEC et actualreceipt. Sortie existante/START existante interdit tout relancement. Les11noms prints exacts doivent tous n'avoir que propext/Classical.choice/Quot.sound ou une liste réellement vide ; tout sorryAx/recovery/autre axiome refusePASS. Aucune distribution vide/standards n'est présupposée avant compilation.

Après un futur FIN : lire vraiment log/receipt, compléter adjudication et completion status réel/modules_passed/declarations_passed/all_current_bytes_preserved, rehash inputs/anciens/archives/captures et dépendance. Hypothétique80/1339 seulement si vraiPASS11 et observationROOT ; aucune promotion actuelle79/1328. Les fautes techniques éventuelles ne seront pas attribuées à la parité. M/H1 uniforme/C5global, coefficientN natif terminé, PP/frontière,D_N/Goldbach/WIN restent ouverts. Aucun lot21 ni nativebuild/banc autorisé par cette préparation.
''')

sources = OWN / "sources"
sources.mkdir(exist_ok=False)
original = BASE / "round22/role3/thermal_gamma_mellin_revision02/ThermalGammaMellinInverse22.lean"
with (sources / original.name).open("xb") as stream:
    stream.write(original.read_bytes())
print("Fresh batch20 tools and exact SOURCE copied; no builder/compiler invoked")
