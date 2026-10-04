"""Generate fresh closure20 text only; never execute/import old closure19."""
from pathlib import Path

OWN = Path(__file__).resolve().parent
text = (OWN.parent / "batch19/close_metadata_once.py").read_text(encoding="utf-8")
text = text.replace("batch19", "batch20").replace("BATCH19", "BATCH20")
text = text.replace("FiniteFieldProjection22", "ThermalGammaMellinInverse22")
text = text.replace("d25eeeb3d508341745e05532f6fd5ef511408c2f7be220334cd2ac4b99721c1c", "8bbe8f7a6989da179664a06b223261dfe947117f8efb328a53849ad334b531c6")
text = text.replace("90fabd8096c829079701138eb43c2acfecf37cea2a30d09a57acf2e5217e078e", "5eaeb84674dccd75b3b651543960a077f0ab31d5a338eab19302945be0790eac")
text = text.replace("0304400125a93cfddace45bcc4428d835c8ee204817f88f156e9fd44ee856f4f", "e9442776bb512a4f83391b63402a1dc86bce61070dfc386bc8b6873af521ce24")
text = text.replace('DEPS = ["QuantizedLambdaEnvelope22", "RationalLogQuantization22"]', 'DEPS = ["GammaPrerequisites22"]')
text = text.replace("(1, 24)", "(1, 11)").replace("(1, 24, 20, 4)", "(1, 11, 9, 2)")
text = text.replace("(8262, 1159, 3089, 29)", "(8456, 1214, 3089, 27)")
text = text.replace("(24, 0, 2, 0, 2)", "(11, 0, 0, 0, 0)")
text = text.replace('assert prop == ["GoldbachThermalGammaMellinInverse22.fieldCharacter", "GoldbachThermalGammaMellinInverse22.fieldCharacter_nat"]', 'assert prop == []')
start, end = text.index("    report = f'''"), text.index('    new(OWN / "adjudication.md", report)')
text = text[:start] + '''    report = f\'''# Lot20 clos : PASS indépendant Γ Mellin11

Unique exécution a58a27/session20281→9a0847 exit0, gate FULL6d61ef SHA {GATE_SHA}, dossier et START absents avant lancement. GlobalSTART {start["time_utc"]}, module {row["started_at"]}→{row["finished_at"]}, globalFIN {fin["time_utc"]}. Un seul enfant ThermalGammaMellinInverse22, aucun timeout/retry/probe/ancien compile/numeric/native build. Commande réelle en START/FIN/reçu, racine sources unique, GammaPrerequisites22 indépendant PASS02 readonly sans recompilation, aucun olean auteur. Source {row["source_sha256"]} immuable ; nouvel olean indépendant SHA {OLEAN_SHA}.

Log, reçu et globalFIN lus FULLaadc49 ; STARTs FULL32c370. Exactement11 déclarations=9 théorèmes+2 définitions et11 prints qualifiés en ordre, chacun avec seulement propext/Classical.choice/Quot.sound. Zéro print sans axiome, zéro print propext seul, zéro sorryAx/recovery/unsafe/native_decide/axiome supplémentaire, aucune erreur ni avertissement. Exit0 et olean neuf acquittent le module auxiliaire entier. L'ancien FAIL18 n'est ni effacé ni rejoué : ses sept diagnostics techniques, six recovery et zéro crédit restent archivés.

Contenu acquis : expKernel et gammaLine réels, continuité et intégrabilité des deux demi-droitesΓ(2±it), réunion par la mesure préservée sous négation, convergence Mellin de exp(−x), identification du transformé àΓ sur Re(s)>0, intégrabilité verticale Re(s)=2 puis inversion réelle et facteur1/(2π) explicite pour x>0. Le majorant2exp(−πt/4) et sa Laplace intégrable viennent de la dépendance indépendanteΓ02. Aucune intégrabilité ou inversion finale n'est posée en prémisse. Cette identité scalaire réelle ne paie pas l'échange avecΛ, le prolongement à a−iθ, M/H1 uniforme ou une annulation arithmétique finale.

Conservation physiquement rehashée :8456inputs/1214anciens Juge/3089archives/27captures, originaux et copies, gate et Gamma02 intacts. PRE SHA {links["PREEXEC.json"]["sha256"]}, POST SHA {links["POSTEXEC.json"]["sha256"]}, actualreceipt SHA {links["receipt.json"]["sha256"]}. GrandsJSON parsés et tous octets liés recontrôlés, aucune fausse qualification rawFULL de toutes sources d'imports. Tous anciens lots et ce20 clos sans reprise. Baseline79/1328 avant observationROOT ; proposition80/1339 limitée à ce nouveau module11. CoefficientN natif terminé, racines/primalités concrètes, raffinement butterflies/mots/GMP/CRT, correctionPP/frontière, D_N, Goldbach et WIN restent ouverts. BUILD04 est une future revue SOURCE distincte ; aucun build ou lot21 autorisé par cette clôture.
\'''
''' + text[end:]
text = text.replace('"declarations_passed": 24', '"declarations_passed": 11')
text = text.replace('"declaration_count_passed": 24', '"declaration_count_passed": 11')
text = text.replace('"theorems_passed": 20, "definitions_passed": 4', '"theorems_passed": 9, "definitions_passed": 2')
text = text.replace('"input_count": 8262, "closed_judge_file_count": 1159, "protected_archive_count": 3089, "capture_count": 29', '"input_count": 8456, "closed_judge_file_count": 1214, "protected_archive_count": 3089, "capture_count": 27')
text = text.replace('"print_count": 24, "standard_print_count": 24', '"print_count": 11, "standard_print_count": 11')
text = text.replace('"previous_official_modules": 78, "previous_official_declarations": 1304', '"previous_official_modules": 79, "previous_official_declarations": 1328')
text = text.replace('"proposed_new_official_modules": 79, "proposed_new_official_declarations": 1328', '"proposed_new_official_modules": 80, "proposed_new_official_declarations": 1339')
text = text.replace('"0d4e79"', '"aadc49"').replace('"c1251a"', '"32c370"')
with (OWN / "close_metadata_once.py").open("x", encoding="utf-8", newline="\n") as stream:
    stream.write(text)
print("New closure20 metadata source generated; not executed")
