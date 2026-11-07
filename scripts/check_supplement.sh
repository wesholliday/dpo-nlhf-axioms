#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

required_files=(
  "README.md"
  "artifact_instructions.txt"
  "SUPPLEMENT_MANIFEST.md"
  "formalization/FORMALIZATION_INDEX.md"
  "formalization/FORMALIZATION_STATUS.md"
  "formalization/FORMALIZATION_COVERAGE.md"
  "formalization/PROOF_FAITHFULNESS.md"
  "formalization/ASSUMPTION_SUMMARY.md"
  "formalization/CITATION_AND_PROVENANCE.md"
  "docs/SUPPLEMENT_PACKAGING.md"
)

for path in "${required_files[@]}"; do
  if [ ! -s "$path" ]; then
    echo "Missing or empty required supplement file: $path" >&2
    exit 1
  fi
done

if [ ! -d "paper/figures" ]; then
  echo "Missing paper/figures directory with generated figure PDFs." >&2
  exit 1
fi

if grep -R -n -E 'FiniteSimplexFixedPoint|FixedPointTheorems|Brouwer|Sperner' \
    formalization/PaperFormalization formalization/PaperFormalization.lean \
    formalization/lakefile.lean; then
  echo "Found a forbidden fixed-point compatibility or Brouwer/Sperner backend reference." >&2
  exit 1
fi

allowed_pdf_pattern='^paper/figures/[^/]+\.pdf$'
if [ -f "paper/main.tex" ] && [ -f "paper/main.pdf" ]; then
  # Source checkouts may keep the compiled paper locally; distributed
  # supplements should omit both paper source and compiled paper PDF.
  allowed_pdf_pattern="^paper/main\.pdf$|$allowed_pdf_pattern"
fi

unexpected_pdfs="$(
  find . -path './.git' -prune -o -path './formalization/.lake' -prune -o -path './.venv' -prune -o -path './.venv_*' -prune -o -path './local_models' -prune -o \
    -name '*.pdf' -print |
    sed 's#^\./##' |
    grep -v -E "$allowed_pdf_pattern" || true
)"
if [ -n "$unexpected_pdfs" ]; then
  echo "Unexpected PDFs found; do not package local copies of external papers:" >&2
  printf '%s\n' "$unexpected_pdfs" >&2
  exit 1
fi

unexpected_large_artifact_dirs="$(
  find . -path './.git' -prune -o -path './formalization/.lake' -prune -o -path './.venv' -prune -o -path './.venv_*' -prune -o -path './local_models' -prune -o \
    \( -name local_models -o -name checkpoints -o -name adapters -o -name wandb \) \
    -type d -print || true
)"
if [ -n "$unexpected_large_artifact_dirs" ]; then
  echo "Unexpected local model/checkpoint artifact directories found:" >&2
  printf '%s\n' "$unexpected_large_artifact_dirs" >&2
  exit 1
fi

cat <<'MSG'
This packaging check does not invoke Lean on the host.
Run `make check-lean-docker` for the isolated Lean audit.
MSG

echo "Supplement check passed."
