#!/usr/bin/env bash
# Build the paper and the arXiv upload tarball.
# Requires Tectonic (brew install tectonic).
set -euo pipefail
cd "$(dirname "$0")"

tectonic -X compile --keep-intermediates --keep-logs main.tex

# arXiv wants the source plus a pre-built .bbl with the same base name.
python3 - <<'EOF'
src = open("main.tex", "rb").read()
assert src.isascii(), "main.tex must stay pure ASCII for pdfLaTeX on arXiv"
EOF
tar -czf arxiv-upload.tar.gz main.tex main.bbl references.bib
echo "wrote main.pdf and arxiv-upload.tar.gz"
tar -tzf arxiv-upload.tar.gz
