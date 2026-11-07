#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# PAPER_SOURCE is interpreted relative to formalization/, unless absolute.
# Use an explicit manuscript path when supplied, otherwise paper/main.tex.
if [ -n "${PAPER_SOURCE:-}" ]; then
  paper_source="$PAPER_SOURCE"
elif [ -f ../paper/main.tex ]; then
  paper_source=../paper/main.tex
else
  paper_source=""
fi
if [ -n "$paper_source" ] && [ ! -f "$paper_source" ]; then
  echo "Paper source not found: $paper_source" >&2
  exit 1
fi
if [ -n "$paper_source" ]; then
  echo "Paper label checks use: $paper_source"
else
  echo "No manuscript included: skipping manuscript label lookup; all Lean and documentation audits still run."
fi

build_log="$(mktemp "${TMPDIR:-/tmp}/ptpv-lean-build.XXXXXX")"
trap 'rm -f "$build_log"' EXIT

lake build 2>&1 | tee "$build_log"

required_reviewer_docs=(
  "FORMALIZATION_INDEX.md"
  "FORMALIZATION_STATUS.md"
  "FORMALIZATION_COVERAGE.md"
  "PROOF_FAITHFULNESS.md"
  "ASSUMPTION_SUMMARY.md"
  "CITATION_AND_PROVENANCE.md"
)
for doc in "${required_reviewer_docs[@]}"; do
  if [ ! -s "$doc" ]; then
    echo "Missing or empty reviewer-facing documentation file: $doc" >&2
    exit 1
  fi
done

for doc in "PROOF_FAITHFULNESS.md" "ASSUMPTION_SUMMARY.md"; do
  if ! grep -F "$doc" FORMALIZATION_INDEX.md >/dev/null; then
    echo "FORMALIZATION_INDEX.md does not point reviewers to $doc." >&2
    exit 1
  fi
done

required_paper_statement_names=(
  "BTProp"
  "DPOasRTBT"
  "Anderson"
  "nlhf-existence"
  "MaxLottProp"
  "PBPM"
  "RTBTPM"
  "NLHFmono"
  "PBPPI"
  "InvolveViolNLHF"
  "InvolveViolRTBT"
  "RTBTorder"
  "NLHFcomm"
)
for name in "${required_paper_statement_names[@]}"; do
  if [ -n "$paper_source" ] && ! grep -F "$name" "$paper_source" >/dev/null; then
    echo "Expected paper statement name not found in $paper_source: $name" >&2
    exit 1
  fi
  if ! grep -F "$name" FORMALIZATION_COVERAGE.md >/dev/null; then
    echo "Expected paper statement name not covered in FORMALIZATION_COVERAGE.md: $name" >&2
    exit 1
  fi
  if ! grep -F "$name" PROOF_FAITHFULNESS.md >/dev/null; then
    echo "Expected paper statement name not discussed in PROOF_FAITHFULNESS.md: $name" >&2
    exit 1
  fi
  if ! grep -F "$name" PaperFormalization/PaperStatements.lean >/dev/null; then
    echo "Expected paper statement name not found in PaperStatements.lean: $name" >&2
    exit 1
  fi
done

if ! grep -F "PaperStatementShapeAudit" PaperFormalization.lean >/dev/null; then
  echo "PaperStatementShapeAudit.lean is not imported by the Lean library root." >&2
  exit 1
fi

if grep -n 'Lean.trustCompiler' "$build_log"; then
  echo "Found Lean.trustCompiler in the paper-facing axiom audit." >&2
  exit 1
fi

project_axiom_refs="$(
  grep -E 'depends on axioms:|^[[:space:]]*PaperFormalization\.' \
      "$build_log" |
    tr -d "'" |
    grep -o -E 'PaperFormalization\.[^] ,:]+' |
    sed -E 's/\.\{[^}]*\}//g' |
    LC_ALL=C sort -u
)"
unexpected_project_axiom_refs="$(
  printf '%s\n' "$project_axiom_refs" |
    grep -v -E '^$' |
    grep -v -E '^PaperFormalization\.PaperStatements\.' || true
)"
if [ -n "$unexpected_project_axiom_refs" ]; then
  echo "Unexpected project-specific dependency in the paper-facing axiom audit:" >&2
  printf '%s\n' "$unexpected_project_axiom_refs" >&2
  exit 1
fi

paper_statement_names="$(
  grep -E '^theorem ' PaperFormalization/PaperStatements.lean |
    sed -E 's/^theorem ([^ :]+).*/\1/' |
    LC_ALL=C sort -u
)"
audit_names="$(
  grep -E '^#print axioms PaperStatements\.' PaperFormalization/AssumptionAudit.lean |
    sed -E 's/^#print axioms PaperStatements\.([^ ]+).*$/\1/' |
    LC_ALL=C sort -u
)"
shape_audit_names="$(
  grep -E '^[[:space:]]*PaperStatements\.' \
      PaperFormalization/PaperStatementShapeAudit.lean |
    grep -o -E 'PaperStatements\.[^ )]+' |
    sed -E 's/^PaperStatements\.//' |
    LC_ALL=C sort -u
)"
missing_audit_names="$(
  comm -23 <(printf '%s\n' "$paper_statement_names") \
    <(printf '%s\n' "$audit_names")
)"
extra_audit_names="$(
  comm -13 <(printf '%s\n' "$paper_statement_names") \
    <(printf '%s\n' "$audit_names")
)"
if [ -n "$missing_audit_names" ]; then
  echo "PaperStatements theorems missing from AssumptionAudit:" >&2
  printf '%s\n' "$missing_audit_names" >&2
  exit 1
fi
if [ -n "$extra_audit_names" ]; then
  echo "AssumptionAudit entries not found in PaperStatements:" >&2
  printf '%s\n' "$extra_audit_names" >&2
  exit 1
fi
missing_shape_audit_names="$(
  comm -23 <(printf '%s\n' "$paper_statement_names") \
    <(printf '%s\n' "$shape_audit_names")
)"
if [ -n "$missing_shape_audit_names" ]; then
  echo "PaperStatements theorems missing from PaperStatementShapeAudit:" >&2
  printf '%s\n' "$missing_shape_audit_names" >&2
  exit 1
fi

if grep -R -n -E '(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)' PaperFormalization; then
  echo "Found sorry/admit in PaperFormalization." >&2
  exit 1
fi

axiom_matches="$(grep -R -n -E '^axiom ' PaperFormalization || true)"
axiom_count="$(printf '%s\n' "$axiom_matches" | sed '/^$/d' | wc -l | tr -d ' ')"
if [ "$axiom_count" != "0" ]; then
  echo "Expected no project axioms, found $axiom_count:" >&2
  printf '%s\n' "$axiom_matches" >&2
  exit 1
fi

if grep -R -n -E 'FiniteSimplexFixedPoint|FixedPointTheorems|Brouwer|Sperner' \
    PaperFormalization PaperFormalization.lean lakefile.lean; then
  echo "Found a forbidden fixed-point compatibility or Brouwer/Sperner backend reference in the active artifact." >&2
  exit 1
fi

echo "Lean artifact check passed."
