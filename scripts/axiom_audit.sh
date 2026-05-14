#!/usr/bin/env bash
#
# scripts/axiom_audit.sh
#
# Reproducible axiom-purity audit for the G26 watchlist of axiom-pure
# theorems. For each watchlist theorem, invokes Lean's `#print axioms`
# command via `lake env lean` on an auto-generated audit module, parses
# the dependency list, and checks compliance against the project's
# axiom whitelist. Output: a Markdown report at
# `audit/axiom_status_<short-sha>.md` pinning the commit, branch, tag,
# toolchain, and date.
#
# Companion to scripts/sorry_audit.sh. Together they constitute the
# double attestation of the watchlist:
#   - sorry_audit:  no `sorry` in code context           (textual)
#   - axiom_audit:  every theorem's transitive axiom     (semantic,
#                   closure is a subset of the whitelist  via Lean)
#
# Usage:
#   ./scripts/axiom_audit.sh              # write audit/axiom_status_<sha>.md
#   ./scripts/axiom_audit.sh --stdout     # print the report to stdout
#   ./scripts/axiom_audit.sh --check      # exit 1 if any whitelist violation
#   ./scripts/axiom_audit.sh --help       # this header
#
# Prerequisites:
#   - lake (Lean 4 build tool) on PATH
#   - The project must already build successfully (lake build); the
#     script does NOT attempt a build itself. Run lake build first.
#
# Side-effects:
#   - Writes (or overwrites) Goldbach/Audit/WatchlistAudit.lean. This
#     file is auto-generated; its header announces "AUTO-GENERATED, do
#     not edit by hand". It is intended to be committed alongside the
#     report so graders can read what was audited.
#
# Excluded paths: not applicable (this audit operates on a fixed
# watchlist, not a file scan).

set -euo pipefail

# ===========================================================================
# CONFIGURATION — edit this section to change watchlist or whitelist
# ===========================================================================

# Watchlist: 11 axiom-pure theorems (fully-qualified names, per manifest v3.0)
WATCHLIST=(
  "Horizon.transfer_bound_at_4"
  "Horizon.transfer_absolute_margin"
  "Horizon.urysohn_smooth"
  "Horizon.C₂_pos"
  "Horizon.C₃_bound"
  "Horizon.Certified.beta_exceeds_half"
  "Horizon.Certified.ci_lower_exceeds_half"
  "Horizon.Certified.fit_quality"
  "Horizon.Certified.A_star_is_finite"
  "Horizon.Certified.dispersion_bound_unconditional"
  "Horizon.Certified.dispersion_converges_to_zero"
)

# Whitelist: axioms permitted to appear in any watchlist theorem's
# transitive dependency closure. Any axiom outside this list flags as
# a violation. Per manifest v3.0 axiom_whitelist field.
WHITELIST=(
  "propext"
  "Classical.choice"
  "Quot.sound"
  "Lean.ofReduceBool"
  "Lean.ofReduceNat"
)

# Imports required by the generated audit module
AUDIT_MODULE_IMPORTS=(
  "Goldbach.G26Verify.HorizonGoldbach"
  "Goldbach.G26Verify.HorizonCertified"
)

# Generated audit module path (relative to repo root)
AUDIT_MODULE_PATH="Goldbach/Audit/WatchlistAudit.lean"

# ===========================================================================

# --- Argument parsing ---
MODE="file"
for arg in "$@"; do
  case "$arg" in
    --stdout) MODE="stdout" ;;
    --check)  MODE="check"  ;;
    -h|--help)
      sed -n '2,38p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *)
      printf 'ERROR: unknown argument: %s\n' "$arg" >&2
      printf 'Try --help.\n' >&2
      exit 2
      ;;
  esac
done

# --- Resolve repo root and metadata ---
REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null)" || {
  printf 'ERROR: must be run inside a git repository\n' >&2
  exit 1
}
cd "$REPO_ROOT"

COMMIT="$(git rev-parse HEAD)"
COMMIT_SHORT="$(git rev-parse --short=7 HEAD)"
TAG_EXACT="$(git describe --tags --exact-match HEAD 2>/dev/null || true)"
TAG_NEAREST="$(git describe --tags --abbrev=0 2>/dev/null || true)"
BRANCH="$(git rev-parse --abbrev-ref HEAD)"
DATE_UTC="$(date -u +'%Y-%m-%dT%H:%M:%SZ')"
if [ -z "$(git status --porcelain 2>/dev/null)" ]; then
  WORKTREE_STATUS="clean"
else
  WORKTREE_STATUS="dirty (uncommitted changes present — output not fully attributable to commit SHA)"
fi
LEAN_VERSION="$(lean --version 2>/dev/null | head -n 1 || echo '(lean not in PATH)')"
LAKE_VERSION="$(lake --version 2>/dev/null | head -n 1 || echo '(lake not in PATH)')"

# --- Check lake availability ---
if ! command -v lake >/dev/null 2>&1; then
  printf 'ERROR: lake (Lean 4 build tool) not on PATH\n' >&2
  printf 'This script requires the project to be built; install Lean 4 and run lake build first.\n' >&2
  exit 3
fi

# --- Generate the audit module ---
AUDIT_DIR="audit"
OUTPUT_FILE="${AUDIT_DIR}/axiom_status_${COMMIT_SHORT}.md"
LEAN_OUT="$(mktemp -t axiom_lean_out_XXXXXX.txt)"
LEAN_ERR="$(mktemp -t axiom_lean_err_XXXXXX.txt)"
AWK_PARSER="$(mktemp -t axiom_parser_XXXXXX.awk)"
TMP_TSV="$(mktemp -t axiom_audit_XXXXXX.tsv)"
trap 'rm -f "$LEAN_OUT" "$LEAN_ERR" "$AWK_PARSER" "$TMP_TSV"' EXIT

mkdir -p "$(dirname "$AUDIT_MODULE_PATH")"
{
  printf '/-\n'
  printf '  AUTO-GENERATED FILE — do not edit by hand.\n'
  printf '  Regenerated by `scripts/axiom_audit.sh` at every run; manual\n'
  printf '  edits will be overwritten.\n\n'
  printf '  Purpose: invoke `#print axioms` on each theorem of the G26\n'
  printf '  axiom-pure watchlist. The stdout of `lake env lean` on this\n'
  printf '  module is parsed by the audit script to verify whitelist\n'
  printf '  compliance.\n\n'
  printf '  Watchlist size: %d theorems.\n' "${#WATCHLIST[@]}"
  printf '  Whitelist size: %d axioms.\n' "${#WHITELIST[@]}"
  printf '%s\n\n' '-/'
  for imp in "${AUDIT_MODULE_IMPORTS[@]}"; do
    printf 'import %s\n' "$imp"
  done
  printf '\n'
  for thm in "${WATCHLIST[@]}"; do
    printf '#print axioms %s\n' "$thm"
  done
} > "$AUDIT_MODULE_PATH"

# --- Run lean and capture output ---
LEAN_EXIT=0
lake env lean "$AUDIT_MODULE_PATH" > "$LEAN_OUT" 2> "$LEAN_ERR" || LEAN_EXIT=$?

if [ "$LEAN_EXIT" -ne 0 ]; then
  printf 'ERROR: lake env lean failed on %s (exit %d)\n' "$AUDIT_MODULE_PATH" "$LEAN_EXIT" >&2
  printf '%s\n' '--- stderr ---' >&2
  cat "$LEAN_ERR" >&2
  printf '%s\n' '--- stdout (partial, may be empty) ---' >&2
  cat "$LEAN_OUT" >&2
  printf '\nHint: ensure `lake build` succeeded for the project, and that every\n' >&2
  printf 'theorem in the watchlist (see the CONFIGURATION block of this script)\n' >&2
  printf 'exists at its fully-qualified name. A typo in WATCHLIST surfaces here\n' >&2
  printf 'as an "unknown identifier" error.\n' >&2
  exit 4
fi

# --- Build awk parser ---
cat > "$AWK_PARSER" <<'AWK_SCRIPT'
# Parser for `#print axioms` output from Lean 4.
# Input: stdout of `lake env lean` on an audit module that contains
# only `#print axioms <name>` commands.
#
# Output (TSV): theorem_name, axiom_count, axiom_list, violation_list, status

BEGIN {
  current_thm = ""
  buffer = ""
  # Whitelist is passed via -v whitelist_str="a,b,c,..."
  n = split(whitelist_str, wl, ",")
  for (i = 1; i <= n; i++) whitelist[wl[i]] = 1
}

function emit(thm, buf,    nw, i, w, c, alist, viol, status) {
  if (thm == "") return
  # Replace brackets and commas in the buffer with spaces, then split
  gsub(/[\[\],]/, " ", buf)
  nw = split(buf, words, /[[:space:]]+/)
  alist = ""
  viol = ""
  c = 0
  for (i = 1; i <= nw; i++) {
    w = words[i]
    if (w == "" || w == "depends" || w == "on" || w == "axioms:") continue
    c++
    alist = alist (alist == "" ? "" : ", ") w
    if (!(w in whitelist)) {
      viol = viol (viol == "" ? "" : ", ") w
    }
  }
  status = (viol == "" ? "PASS" : "FAIL")
  if (c == 0) {
    alist = "(none)"
  }
  if (viol == "") {
    viol = "(none)"
  }
  printf "%s\t%d\t%s\t%s\t%s\n", thm, c, alist, viol, status
}

# Pattern 1: 'X' depends on axioms: [a, b, c]   (may wrap across lines)
/^'[^']+' depends on axioms:/ {
  if (current_thm != "") emit(current_thm, buffer)
  match($0, /^'[^']+'/)
  current_thm = substr($0, RSTART + 1, RLENGTH - 2)
  pos = index($0, "axioms:") + 7
  buffer = substr($0, pos)
  next
}

# Pattern 2: 'X' does not depend on any axioms
/^'[^']+' does not depend on any axioms/ {
  if (current_thm != "") emit(current_thm, buffer)
  match($0, /^'[^']+'/)
  current_thm = substr($0, RSTART + 1, RLENGTH - 2)
  emit(current_thm, "")
  current_thm = ""
  buffer = ""
  next
}

# Continuation line: append to buffer if we are inside a list
current_thm != "" && length($0) > 0 {
  buffer = buffer " " $0
}

END {
  if (current_thm != "") emit(current_thm, buffer)
}
AWK_SCRIPT

# Build whitelist as comma-separated string
WL_STR=""
for w in "${WHITELIST[@]}"; do
  WL_STR+="${WL_STR:+,}${w}"
done

awk -v whitelist_str="$WL_STR" -f "$AWK_PARSER" "$LEAN_OUT" > "$TMP_TSV"

# --- Tallies ---
TOTAL_EXPECTED="${#WATCHLIST[@]}"
TOTAL_FOUND="$(wc -l < "$TMP_TSV" | tr -d ' ')"
TOTAL_PASS="$(awk -F'\t' '$5 == "PASS"' "$TMP_TSV" | wc -l | tr -d ' ')"
TOTAL_FAIL="$(awk -F'\t' '$5 == "FAIL"' "$TMP_TSV" | wc -l | tr -d ' ')"
TOTAL_MISSING=$((TOTAL_EXPECTED - TOTAL_FOUND))

# --- Render markdown report ---
render_report() {
  printf '# Axiom-Purity Audit — `goldbach-horizon`\n\n'
  printf '**Commit:** `%s` (short: `%s`)  \n' "$COMMIT" "$COMMIT_SHORT"
  if [ -n "$TAG_EXACT" ]; then
    printf '**Tag at HEAD:** `%s`  \n' "$TAG_EXACT"
  else
    printf '**Tag at HEAD:** *none* (nearest: `%s`)  \n' "${TAG_NEAREST:-none}"
  fi
  printf '**Branch:** `%s`  \n' "$BRANCH"
  printf '**Worktree status:** %s  \n' "$WORKTREE_STATUS"
  printf '**Audit date (UTC):** `%s`  \n' "$DATE_UTC"
  printf '**Toolchain:**\n\n'
  printf -- '- `%s`\n' "$LEAN_VERSION"
  printf -- '- `%s`\n\n' "$LAKE_VERSION"
  printf '**Generated audit module:** `%s` (auto-regenerated each run)\n\n' "$AUDIT_MODULE_PATH"
  printf -- '---\n\n'

  printf '## Summary\n\n'
  printf '| Metric | Count |\n'
  printf '|---|---|\n'
  printf '| Watchlist size (expected) | %d |\n' "$TOTAL_EXPECTED"
  printf '| Theorems audited (found in Lean output) | %d |\n' "$TOTAL_FOUND"
  printf '| Theorems missing from Lean output | %d |\n' "$TOTAL_MISSING"
  printf '| PASS (axioms ⊆ whitelist) | %d |\n' "$TOTAL_PASS"
  printf '| FAIL (at least one non-whitelist axiom) | %d |\n' "$TOTAL_FAIL"
  printf '\n'

  if [ "$TOTAL_MISSING" -gt 0 ]; then
    printf '⚠ **%d theorem(s) absent from Lean output.** Most likely cause: typo in the watchlist FQN, or the theorem has been renamed/removed. Compare against the WATCHLIST array in `scripts/axiom_audit.sh`.\n\n' "$TOTAL_MISSING"
  fi

  if [ "$TOTAL_FAIL" -gt 0 ]; then
    printf '❌ **%d whitelist violation(s) detected.** Re-run with `--check` to get exit code 1 for CI use.\n\n' "$TOTAL_FAIL"
  elif [ "$TOTAL_MISSING" -eq 0 ]; then
    printf '✅ **All %d watchlist theorems verified axiom-pure under the whitelist.**\n\n' "$TOTAL_EXPECTED"
  fi

  printf -- '---\n\n'

  printf '## Whitelist (active)\n\n'
  for w in "${WHITELIST[@]}"; do
    printf -- '- `%s`\n' "$w"
  done
  printf '\n'

  printf '## Per-theorem detail\n\n'
  printf '| Status | Theorem | # axioms | Axioms | Violations |\n'
  printf '|---|---|---|---|---|\n'

  # Walk the watchlist in declaration order so the report ordering is stable
  for thm in "${WATCHLIST[@]}"; do
    row="$(awk -F'\t' -v t="$thm" '$1 == t' "$TMP_TSV")"
    if [ -z "$row" ]; then
      printf '| ❓ MISSING | `%s` | — | — | not present in Lean output |\n' "$thm"
    else
      IFS=$'\t' read -r t count alist viol status <<< "$row"
      icon="✅"
      [ "$status" = "FAIL" ] && icon="❌"
      # awk emits "(none)" for empty violations; render as em-dash for readability
      viol_cell="$viol"
      [ "$viol_cell" = "(none)" ] && viol_cell="—"
      printf '| %s %s | `%s` | %d | %s | %s |\n' \
        "$icon" "$status" "$t" "$count" "$alist" "$viol_cell"
    fi
  done
  printf '\n'

  if [ "$TOTAL_FAIL" -gt 0 ]; then
    printf '## Violation detail\n\n'
    awk -F'\t' '$5 == "FAIL" {
      printf "### `%s`\n\n", $1
      printf "Non-whitelist axioms: `%s`  \n", $4
      printf "Full axiom set: `%s`\n\n", $3
    }' "$TMP_TSV"
  fi

  printf -- '---\n\n## Reproducibility\n\n'
  printf 'To regenerate this report at the same commit on a clean worktree:\n\n'
  printf '```bash\n'
  printf 'git checkout %s\n' "$COMMIT"
  printf 'lake build                  # ensure all dependencies are built\n'
  printf './scripts/axiom_audit.sh\n'
  printf '```\n\n'
  printf 'The output filename is keyed on the short commit SHA. Re-running on the same commit with a clean worktree and a deterministic Lean build produces a byte-identical report (modulo the `Audit date (UTC)` field and the `Toolchain` block, which depend on environment).\n\n'

  printf '## Detection logic\n\n'
  printf '1. Generate `%s` from the WATCHLIST array (a sequence of `#print axioms` calls, one per theorem, plus the project imports).\n' "$AUDIT_MODULE_PATH"
  printf '2. Invoke `lake env lean` on the generated module; capture stdout (axiom messages) separately from stderr (build errors).\n'
  printf '3. Single-pass `awk` parser: for every `'\''X'\'' depends on axioms: [...]` and `'\''X'\'' does not depend on any axioms` line, extract the theorem name and accumulate the axiom list (lists may wrap across lines).\n'
  printf '4. For each parsed row, compare the axiom set against the WHITELIST array; flag any axiom outside the whitelist as a violation.\n'
  printf '5. Render Markdown with per-theorem rows in WATCHLIST declaration order (so the report ordering is stable across runs and matches the manifest).\n\n'

  printf '## Known limitations\n\n'
  printf -- '- **Requires a successful project build.** If `lake build` has not been run (or has failed), this script exits 4 with the Lean error output. Build first.\n'
  printf -- '- **The audit is byte-faithful to whatever `#print axioms` reports.** If Lean is configured to suppress or rewrite axiom messages (unusual), the script cannot recover the missing data.\n'
  printf -- '- **No protection against malicious axiom redefinition.** A project that adds an axiom named `propext` of a different type would silently pass; the whitelist matches by name only. Protection against axiom shadowing is the Lean kernel'\''s responsibility.\n'
  printf -- '- **The script regenerates `%s` every run.** Manual edits to that file are lost. To change the audit scope, edit the WATCHLIST/WHITELIST arrays in this script and re-run.\n' "$AUDIT_MODULE_PATH"
  printf -- '- **`Lean.ofReduceNat` is in the whitelist but may not appear in any current theorem'\''s closure** (per manifest v3.0 note: only `Lean.ofReduceBool` is observed, on `Horizon.C₂_pos`). The whitelist is deliberately broader than the observable to absorb future migrations.\n'
}

# --- Dispatch ---
case "$MODE" in
  stdout)
    render_report
    ;;
  check)
    if [ "$TOTAL_FAIL" -gt 0 ] || [ "$TOTAL_MISSING" -gt 0 ]; then
      if [ "$TOTAL_FAIL" -gt 0 ]; then
        printf 'FAIL: %d whitelist violation(s) at commit %s\n' \
          "$TOTAL_FAIL" "$COMMIT_SHORT" >&2
      fi
      if [ "$TOTAL_MISSING" -gt 0 ]; then
        printf 'FAIL: %d watchlist theorem(s) missing from Lean output at commit %s\n' \
          "$TOTAL_MISSING" "$COMMIT_SHORT" >&2
      fi
      exit 1
    fi
    printf 'OK: all %d watchlist theorems pass whitelist at commit %s\n' \
      "$TOTAL_EXPECTED" "$COMMIT_SHORT"
    ;;
  file)
    mkdir -p "$AUDIT_DIR"
    render_report > "$OUTPUT_FILE"
    printf 'Axiom audit report written:\n'
    printf '  path:       %s\n' "$OUTPUT_FILE"
    printf '  audited:    %d / %d\n' "$TOTAL_FOUND" "$TOTAL_EXPECTED"
    printf '  pass:       %d\n' "$TOTAL_PASS"
    printf '  fail:       %d\n' "$TOTAL_FAIL"
    printf '  missing:    %d\n' "$TOTAL_MISSING"
    if [ -n "$TAG_EXACT" ]; then
      printf '  commit:     %s (%s)\n' "$COMMIT_SHORT" "$TAG_EXACT"
    else
      printf '  commit:     %s (no exact tag at HEAD)\n' "$COMMIT_SHORT"
    fi
    printf '  aux module: %s (regenerated)\n' "$AUDIT_MODULE_PATH"
    ;;
esac
