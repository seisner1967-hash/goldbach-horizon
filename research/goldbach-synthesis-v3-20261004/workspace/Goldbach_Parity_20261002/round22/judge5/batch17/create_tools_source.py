"""New tools/copies by text only; old batch16 never imported or executed."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
JUDGE = OWN.parent
BASE = JUDGE.parents[1]
OLD = JUDGE / "batch16"

def put(name, text):
    with (OWN / name).open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(text)

builder = (OLD / "prepare_metadata.py").read_text(encoding="utf-8").replace("batch16", "batch17").replace("BATCH16", "BATCH17")
builder = builder.replace("role3/log_quantization_source22/revision02", "role3/log_quantization_source22/revision03")
builder = builder.replace("9e59eb6b8aa4efcb5cc6cdc27d7d7a7d24517986fcd1ad2b4413b97c0efc1fb0", "dfabcabf39ecc1ba7769eb99ea73e0483dc6925f0bb3d11c05891d22c0a787a7")
builder = builder.replace('"87a11a"', '"3b5d94"').replace('"a87644"', '"528830"')
start = builder.index("    support = [")
end = builder.index("    for path, digest, chunk in support:", start)
builder = builder[:start] + '''    support = [
        (JUDGE / "log_quantization_source_review_revision03.md", "4e970b56e55f461999f04350258b74da862178b791916222ccc7af2d6948715b", "193afc"),
        (JUDGE / "log_quantization_source_review_revision02.md", "a8b74e2d2132ad40f0caa44e49ebd14cca234993bd0fd26f30ad83f15c5fcb65", "2bccd7"),
        (BASE / "round22/role3/log_quantization_source22/revision03/dependency_contract22.md", "1f7540a4f3f6ab246ecbb5440fb3bce4010e53e51947652a19e5bc28f9301f91", "7cc51d"),
        (BASE / "round22/role3/log_quantization_source22/revision03/source_manifest22.json", "0a80e90f2f9a959df868599a5d85e19438630a443a87dd38cf313b914e078845", "7cc51d"),
        (BASE / "round22/role3/log_quantization_source22/revision03/read_receipts22.json", "4de64ad7d6d2bd29667707ed2ddbfd9893bce796540644d9e933d0c8ff15af05", "7cc51d"),
        (JUDGE / "batch16/adjudication.md", "9276ac7bfa386ec38c2ebde884a575137b3bea723e64124a46962455f6c79c69", "e20100"),
        (JUDGE / "batch16/completion_receipt.json", "455e5ae4bf0907b9ea2ac2ece90a0c578b0f3f3cf430a5d3d2a61402bbd6b8bc", "e20100"),
        (JUDGE / "batch16/batch16_attempt01/receipt.json", "1632ce21dee28fd87c4d08958797787d551f2c5937b540c469a5e7600ef3d09c", "3f0ffa"),
        (JUDGE / "batch16/batch16_attempt01/RationalLogQuantization22.log", "45311354041cb407df0372b3f764bdb2bf90ea66b0a3100b1b072945510ef5c6", "9acef7")]
''' + builder[end:]
start = builder.index("    api_reads = [")
end = builder.index("    for relative, chunk, scope in api_reads:", start)
builder = builder[:start] + '''    api_reads = [
        ("Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean", "054dec/43d8fc", "TARGETED_272_299_PLUS_RG283_285"),
        ("Mathlib/Topology/Algebra/InfiniteSum/Basic.lean", "f76bef", "TARGETED_52_75"),
        ("Mathlib/Data/Rat/Cast/Order.lean", "f76bef", "TARGETED_1_102"),
        ("Mathlib/Data/Rat/Cast/Defs.lean", "f76bef", "TARGETED_65_160"),
        ("Mathlib/Data/Rat/Cast/CharZero.lean", "f76bef", "TARGETED_25_110"),
        ("Mathlib/Topology/Algebra/InfiniteSum/NatInt.lean", "054dec", "TARGETED_197_234"),
        ("Mathlib/Topology/Algebra/InfiniteSum/Order.lean", "054dec", "TARGETED_30_61"),
        ("Mathlib/Data/Nat/Log.lean", "054dec/b3b8e6", "TARGETED_208_234_106_150"),
        ("Mathlib/Analysis/SpecificLimits/Basic.lean", "b3b8e6", "TARGETED_278_300"),
        ("Mathlib/NumberTheory/VonMangoldt.lean", "b3b8e6", "TARGETED_58_86"),
        ("Mathlib/Data/Nat/Prime/Defs.lean", "b3b8e6", "TARGETED_254_284"),
        ("Mathlib/Algebra/Order/Floor.lean", "b3b8e6", "TARGETED_642_680")]
''' + builder[end:]
put("prepare_metadata.py", builder)
launcher = (OLD / "run_once.py").read_text(encoding="utf-8").replace("batch16", "batch17").replace("BATCH16", "BATCH17")
put("run_once.py", launcher)
(OWN / "sources").mkdir(exist_ok=False)
for module in ("RationalLogQuantization22", "QuantizedLambdaEnvelope22"):
    source = BASE / "round22/role3/log_quantization_source22/revision03" / (module + ".lean")
    with (OWN / "sources" / (module + ".lean")).open("xb") as stream:
        stream.write(source.read_bytes())
put("preparation.md", '''# Lot 17 — préparation indépendante SOURCE52 révision03

Sélection ROOT contingente satisfaite par revue SOURCE03 close sans déficit précis : log_quantization_source_review_revision03.md4e970b56… FULL193afc. Sources auteurs FULL3b5d94 et528830 ; docs FULL7cc51d, API TARGETED43d8fc/f76bef et anciennes lectures qualifiées. Rational dfabcabf…38=23thm15defs puis Envelope526354f4…14=9thm5defs ; deux modules52=32thm20defs52prints. Metadataa53e36 a vérifié52headers/domaines,20définitions et52prints inchangés. Le FAIL16 réel4API,9sorryAx recovery reste clos et zéro crédit ; aucune ancienne copie/révision ou olean n'est réutilisé comme résultat.

Le HasSum.congr_fun porte le terme appliqué avec les castsNat complets. Rat.cast_le puis cast_abs/sub/intCast/div/one/ofNat résolvent sur SOURCE les trois conversions rationnel→réel. Vraie série/log32, reste géométrique, nearest-even et clamp donnent précision1/S sans précision libre. Le second module vraieLambda/IsPrimePow/minFac conserve toutesPP, construitbornes32/erreurs64/S/sommefinie, E=(N+1)(64/S+1/S²) et continuité surs>0. Précision pourS2^58 fixé,N≤1e8. Aucune cible ou majorantfinalsupposé ; zéroD_N/WIN. Native commonD/catalogue/mots/NTTCRT/coefficientN,H1global etPPfront restent ouverts.

Nouveaux outils lus FULL avant unique builder metadata. Le générateur lit les outils16 comme texte, jamais import ou exécution ancienne. Catalogue52/qualifiedprints/absence tokens interdits horscomments et copiesbyteexactes ; commonroot batch17/sources vérifié pour TOUSmodules. Fermeture exhaustive source+cacheolean depuis8packages et Init/Prelude, import localRational exclu des caches : seul son nouvelolean du premier enfant peut alimenterEnvelope. readonly_oleans vide, aucune ancienne dépendance/olean auteur autorisé ; LEAN_PATH outputneuf puis readonlyvide puis huitcache. Importsmathlib mathFULL nonprétendus ; grands JSON tousbytes/hash+headerprojection honnête.

Gate17 distincte impérative avant Lean : une unique batch17_attempt01,max2children300schacun/-DmaxHeartbeats1000000,ordreRational→Envelope stopfirstFAIL puisNON_INVOKED. Parser audit exact ordre/noms et listesaxiomesstandards seulement ; emptyaxioms légitimes acceptés/listés, sorryAx/recovery/missingprints refusés. PRE/STARTglobalmodules/command/logstdoutstderr/FIN/olean/POST/receipt réels et conservationtousinputs+copies/gate/3089archives. Sourcesetoldlots01–16 définitivementreadonly ; aucune installation/git/probe/oldrecompile/retry/numericbank.

Baseline officielle ROOT16observé76modules1252aux ; hypothétique78/1304 seulementsi deux vraisPASS etobserverROOT. AucunPASS source anticipé. PythonSHA4278cf2a… fixé-B-Xutf8,Lean4.15SHA8a1ef185…,mathlib9837ca9d inchangés. Audit native01 gelé6d6899… est séparé/horslot17 ; aucunbuild numérique n'est autorisé par cette préparation.
''')
print("NEW_BATCH17_TEXT_TOOLS_AND_TWO_SOURCE_COPIES_CREATED_ONLY")
