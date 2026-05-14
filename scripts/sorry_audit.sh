#!/usr/bin/env bash
#
# scripts/sorry_audit.sh
#
# Reproducible audit of `sorry` occurrences in the goldbach-horizon Lean
# source tree. Walks every `*.lean` file under the repository root, strips
# Lean comments, and reports each `sorry` token in code context together
# with the enclosing top-level declaration. Output is a Markdown report at
# `audit/sorry_status_<short-sha>.md` pinning the commit, branch, tag,
# toolchain, and date — so re-running the script at the same commit on a
# clean worktree produces a byte-identical report.
#
# Usage:
#   ./scripts/sorry_audit.sh              # write audit/sorry_status_<sha>.md
#   ./scripts/sorry_audit.sh --stdout     # print the report to stdout
#   ./scripts/sorry_audit.sh --check      # exit 1 if any sorry found (CI use)
#   ./scripts/sorry_audit.sh --help       # this header
#
# Portability: Bash + awk + standard POSIX utilities. Tested on Bash 4+
# (Linux, macOS) and Git Bash on Windows. No Python, no Lean toolchain
# required for the audit itself (Lean version is recorded as metadata
# only, on a best-effort basis).
#
# Excluded paths: `.lake/`  `build/`  `lake-packages/`  `.git/`
#
# Detection scope:
#   - Detects literal `sorry` at word boundaries in non-comment code.
#   - Strips line comments (`--`) and nested block comments (`/- ... -/`).
#   - Does NOT detect transitively imported `sorryAx` from dependencies
#     (Mathlib etc.). For that, use `#print axioms <decl>` per theorem
#     or rely on the project's axiom-purity whitelist gate.
#   - Does NOT detect `sorry` inside macro quotations `` `(...) `` (rare
#     in goldbach-horizon; flag any false positive manually).

set -euo pipefail

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------
MODE="file"
for arg in "$@"; do
  case "$arg" in
    --stdout) MODE="stdout" ;;
    --check)  MODE="check"  ;;
    -h|--help)
      sed -n '2,32p' "$0" | sed 's/^# \{0,1\}//'
      exit 0
      ;;
    *)
      printf 'ERROR: unknown argument: %s\n' "$arg" >&2
      printf 'Try --help.\n' >&2
      exit 2
      ;;
  esac
done

# ---------------------------------------------------------------------------
# Resolve repo root and capture metadata
# ---------------------------------------------------------------------------
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

AUDIT_DIR="audit"
OUTPUT_FILE="${AUDIT_DIR}/sorry_status_${COMMIT_SHORT}.md"

# ---------------------------------------------------------------------------
# Scanner: single-pass awk that strips comments, tracks declarations, and
# emits one TSV row per `sorry` token in code context.
# ---------------------------------------------------------------------------
SCAN_SCRIPT="$(mktemp -t sorry_scan_XXXXXX.awk)"
TMP_TSV="$(mktemp -t sorry_audit_XXXXXX.tsv)"
trap 'rm -f "$SCAN_SCRIPT" "$TMP_TSV"' EXIT

cat > "$SCAN_SCRIPT" <<'AWK_SCRIPT'
# TSV columns emitted: file, line, decl_name, decl_kind, raw_source_line
#
# Algorithm:
#   For each file (FNR == 1 resets state):
#     For each line:
#       1. Strip Lean comments into `stripped`, preserving column offsets
#          by replacing comment chars with spaces. Block comments are
#          nestable per Lean 4 spec; tracked via `depth` counter.
#       2. If the stripped line begins a top-level declaration, update
#          the (decl_name, decl_kind) state.
#       3. If the stripped line contains a `sorry` token at word
#          boundaries (excluding `sorryAx`, `mysorry`, `sorry!`), emit
#          a TSV row.

FNR == 1 {
  depth = 0
  decl  = "(file-scope)"
  kind  = "-"
}

function update_decl(text,    i, pat, mods, kws, changed) {
  # Strip leading whitespace
  sub(/^[[:space:]]+/, "", text)
  # Strip @[attribute] prefixes (possibly multiple)
  while (match(text, /^@\[[^]]*\][[:space:]]+/)) {
    text = substr(text, RLENGTH + 1)
  }
  # Strip declaration modifiers
  changed = 1
  while (changed) {
    changed = 0
    split("private protected public noncomputable partial unsafe nonrec scoped mutual", mods, " ")
    for (i in mods) {
      pat = "^" mods[i] "[[:space:]]+"
      if (match(text, pat)) {
        text = substr(text, RLENGTH + 1)
        changed = 1
        break
      }
    }
  }
  # Match a top-level keyword and capture the identifier that follows
  split("theorem lemma def example instance abbrev structure inductive class axiom opaque", kws, " ")
  for (i in kws) {
    pat = "^" kws[i] "[[:space:]]+"
    if (match(text, pat)) {
      text = substr(text, RLENGTH + 1)
      if (match(text, /^[A-Za-z_][A-Za-z0-9_'.]*/)) {
        decl = substr(text, 1, RLENGTH)
        kind = kws[i]
        return
      }
      # Keyword matched but no name follows: anonymous example / instance
      # (`example : ... := ...` and `instance : ... where ...` are common
      # Lean 4 idioms). Attribute the next sorry to a synthetic name so
      # the audit does not silently inherit the previous declaration.
      if (kws[i] == "example" || kws[i] == "instance") {
        decl = "(anonymous " kws[i] ")"
        kind = kws[i]
      }
      return
    }
  }
}

{
  raw = $0
  stripped = ""
  i = 1
  n = length(raw)
  while (i <= n) {
    two = substr(raw, i, 2)
    if (depth > 0) {
      # Inside a block comment
      if (two == "-/") {
        depth--
        stripped = stripped "  "
        i += 2
      } else if (two == "/-") {
        depth++
        stripped = stripped "  "
        i += 2
      } else {
        stripped = stripped " "
        i++
      }
    } else {
      # Outside any comment
      if (two == "/-") {
        depth++
        stripped = stripped "  "
        i += 2
      } else if (two == "--") {
        # Line comment from here to end of line — pad with spaces and stop
        while (i <= n) { stripped = stripped " "; i++ }
        break
      } else {
        stripped = stripped substr(raw, i, 1)
        i++
      }
    }
  }

  # Update declaration tracker if this stripped line starts a declaration
  update_decl(stripped)

  # Word-boundary `sorry` detection in the stripped (non-comment) content
  if (match(stripped, /(^|[^A-Za-z0-9_'])sorry([^A-Za-z0-9_'!]|$)/)) {
    # Sanitize raw line for TSV (replace literal TAB with 4 spaces)
    safe_raw = raw
    gsub(/\t/, "    ", safe_raw)
    printf "%s\t%d\t%s\t%s\t%s\n", FILENAME, FNR, decl, kind, safe_raw
  }
}
AWK_SCRIPT

# ---------------------------------------------------------------------------
# Find Lean files and scan them in a single awk invocation
# ---------------------------------------------------------------------------
# Using -print0 / sort -z / xargs -0 to be safe against paths containing
# spaces. xargs without -I {} passes all files in one awk invocation, so
# FILENAME and FNR work naturally.
find . -type f -name '*.lean' \
  -not -path './.lake/*' \
  -not -path './build/*' \
  -not -path './lake-packages/*' \
  -not -path './.git/*' \
  -print0 \
  | sort -z \
  | xargs -0 -r awk -f "$SCAN_SCRIPT" \
  > "$TMP_TSV"

HIT_COUNT="$(wc -l < "$TMP_TSV" | tr -d ' ')"

# ---------------------------------------------------------------------------
# Markdown rendering
# ---------------------------------------------------------------------------
render_report() {
  printf '# `sorry` Audit — `goldbach-horizon`\n\n'
  printf '**Commit:** `%s` (short: `%s`)  \n' "$COMMIT" "$COMMIT_SHORT"
  if [ -n "$TAG_EXACT" ]; then
    printf '**Tag at HEAD:** `%s`  \n' "$TAG_EXACT"
  else
    printf '**Tag at HEAD:** *none* (nearest: `%s`)  \n' "${TAG_NEAREST:-none}"
  fi
  printf '**Branch:** `%s`  \n' "$BRANCH"
  printf '**Worktree status:** %s  \n' "$WORKTREE_STATUS"
  printf '**Audit date (UTC):** `%s`  \n' "$DATE_UTC"
  printf '**Toolchain (best-effort, metadata only):**\n\n'
  printf -- '- `%s`\n' "$LEAN_VERSION"
  printf -- '- `%s`\n\n' "$LAKE_VERSION"
  printf -- '---\n\n'

  printf '## Summary\n\n'
  printf '**Total `sorry` tokens detected in code context:** %s\n\n' "$HIT_COUNT"

  if [ "$HIT_COUNT" -eq 0 ]; then
    printf 'No `sorry` token was detected in any `.lean` file under the repository root (excluding `.lake/`, `build/`, `lake-packages/`, `.git/`).\n\n'
    printf 'This is a *necessary but not sufficient* condition for full proof closure: transitively imported `sorryAx` from Mathlib or other dependencies is NOT detected by this script. For axiom-level auditing, use `#print axioms <decl>` per theorem (or the project'\''s whitelist gate).\n\n'
  else
    # Breakdown by file
    printf '### By file\n\n'
    printf '| File | Count |\n'
    printf '|---|---|\n'
    awk -F'\t' '{print $1}' "$TMP_TSV" \
      | sed 's|^\./||' \
      | sort | uniq -c \
      | awk '{count=$1; $1=""; sub(/^[ \t]+/,""); printf "| `%s` | %d |\n", $0, count}'
    printf '\n'

    # Breakdown by declaration kind
    printf '### By declaration kind\n\n'
    printf '| Kind | Count |\n'
    printf '|---|---|\n'
    awk -F'\t' '{print $4}' "$TMP_TSV" \
      | sort | uniq -c \
      | awk '{printf "| %s | %d |\n", $2, $1}'
    printf '\n'

    # Detail, grouped by file
    printf -- '---\n\n## Detail\n\n'
    printf 'Each row is a single `sorry` token in non-comment code. **Declaration** is the nearest preceding top-level declaration on the strip-of-comments view (so it is robust against doc-comments and `/- ... -/` blocks intervening). **Kind** is the Lean keyword. **Source line** is the raw line as written in the file (TABs replaced with 4 spaces, `|` and backticks escaped for Markdown).\n\n'

    current_file=""
    while IFS=$'\t' read -r f ln d k raw; do
      f_short="${f#./}"
      if [ "$f_short" != "$current_file" ]; then
        printf '\n### `%s`\n\n' "$f_short"
        printf '| Line | Kind | Declaration | Source line |\n'
        printf '|---|---|---|---|\n'
        current_file="$f_short"
      fi
      # Escape backslashes first (must be first), then | and `
      raw_md="$(printf '%s' "$raw" \
        | sed -e 's/\\/\\\\/g' -e 's/|/\\|/g' -e 's/`/\\`/g')"
      printf '| %s | %s | `%s` | `%s` |\n' "$ln" "$k" "$d" "$raw_md"
    done < "$TMP_TSV"
    printf '\n'
  fi

  printf -- '---\n\n## Reproducibility\n\n'
  printf 'To regenerate this report at the same commit on a clean worktree:\n\n'
  printf '```bash\n'
  printf 'git checkout %s\n' "$COMMIT"
  printf './scripts/sorry_audit.sh\n'
  printf '```\n\n'
  printf 'The output filename is keyed on the short commit SHA. Re-running on the same commit with a clean worktree overwrites the same file and produces byte-identical content (modulo the `Audit date (UTC)` field and the `Toolchain` block, which depend on environment).\n\n'
  printf 'For diff-friendly archival, the report can be normalised by:\n\n'
  printf '```bash\n'
  printf './scripts/sorry_audit.sh --stdout \\\n'
  printf '  | sed -E '\''s/^\*\*Audit date.*/[date-stripped]/; s/^- `Lean.*/[lean-stripped]/; s/^- `Lake.*/[lake-stripped]/'\'' \\\n'
  printf '  > audit/sorry_status_%s_normalised.md\n' "$COMMIT_SHORT"
  printf '```\n\n'

  printf '## Detection logic\n\n'
  printf '1. Walk every `*.lean` under the repository root, excluding `.lake/`, `build/`, `lake-packages/`, `.git/`. Sort the file list (so output ordering is reproducible across filesystems).\n'
  printf '2. For each file, single-pass `awk` scanner:\n'
  printf '   - Tracks block comment depth (`/- ... -/`, nestable per Lean 4 spec).\n'
  printf '   - Strips line comments (`--` to end of line).\n'
  printf '   - Replaces stripped comment characters with spaces (preserves column alignment for reporting).\n'
  printf '   - Updates the current declaration name and kind on every line that matches a top-level declaration header (`theorem`/`lemma`/`def`/`example`/`instance`/`abbrev`/`structure`/`inductive`/`class`/`axiom`/`opaque`, possibly preceded by `@[attribute]` and modifiers `private`/`protected`/`noncomputable`/`partial`/`unsafe`/`nonrec`/`scoped`/`mutual`).\n'
  printf '   - Emits a TSV row for every line whose stripped content contains a `sorry` token at word boundaries.\n'
  printf '3. Render TSV as Markdown with metadata header, two summary tables (by file, by kind), and per-file detail tables.\n\n'

  printf '## Known limitations\n\n'
  printf -- '- **Macro quotation is not parsed**: a `sorry` inside `` `(...) `` would be detected as a plain `sorry`. False-positive risk: low in this codebase.\n'
  printf -- '- **Transitive axioms are invisible**: a dependency contributing `sorryAx` is not detected. Run `#print axioms <decl>` per theorem.\n'
  printf -- '- **Multi-line declaration headers**: if the keyword and the name straddle multiple lines (unusual), the tracker may misattribute the next `sorry`. Inspect manually for any unexpected `(file-scope)` attributions.\n'
  printf -- '- **`Term.byTacticSeq` placeholders**: idiomatic `:= by sorry` is detected normally; `:= by { sorry }` is also detected.\n'
  printf -- '- **`scoped` and `mutual` blocks**: `scoped theorem foo` is correctly attributed; `mutual ... end` blocks track only the last entered declaration before a `sorry`.\n'
}

# ---------------------------------------------------------------------------
# Dispatch
# ---------------------------------------------------------------------------
case "$MODE" in
  stdout)
    render_report
    ;;
  check)
    if [ "$HIT_COUNT" -gt 0 ]; then
      printf 'FAIL: %s sorry occurrence(s) detected at commit %s\n' \
        "$HIT_COUNT" "$COMMIT_SHORT" >&2
      printf 'Run without --check to write the full report.\n' >&2
      exit 1
    fi
    printf 'OK: no sorry occurrences at commit %s\n' "$COMMIT_SHORT"
    ;;
  file)
    mkdir -p "$AUDIT_DIR"
    render_report > "$OUTPUT_FILE"
    printf 'Audit report written:\n'
    printf '  path:   %s\n' "$OUTPUT_FILE"
    printf '  hits:   %s\n' "$HIT_COUNT"
    if [ -n "$TAG_EXACT" ]; then
      printf '  commit: %s (%s)\n' "$COMMIT_SHORT" "$TAG_EXACT"
    else
      printf '  commit: %s (no exact tag at HEAD)\n' "$COMMIT_SHORT"
    fi
    ;;
esac
