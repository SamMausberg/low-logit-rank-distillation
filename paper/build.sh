#!/bin/sh
# Build low_logit_rank_distillation.pdf in a temporary directory and copy it back.
# Requires pdfLaTeX with the packages listed in the preamble.
set -e
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cp "$here/low_logit_rank_distillation.tex" "$tmp/"
cd "$tmp"
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error low_logit_rank_distillation.tex > "$here/build.log" 2>&1
done
if grep -q "Rerun to get" low_logit_rank_distillation.log; then
  echo "cross-references did not settle" >&2
  exit 1
fi
cp low_logit_rank_distillation.pdf "$here/"
echo "built $here/low_logit_rank_distillation.pdf"
