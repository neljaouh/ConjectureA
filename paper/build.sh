#!/usr/bin/env bash
# Build the paper and the arXiv upload tarball.
# Requires Tectonic (brew install tectonic).
set -euo pipefail
cd "$(dirname "$0")"

name=applegate-lagarias-conjecture-a-proof
tectonic -X compile --keep-intermediates --keep-logs "$name.tex"

# arXiv wants the source plus a pre-built .bbl with the same base name.
python3 - "$name.tex" <<'EOF'
import sys
src = open(sys.argv[1], "rb").read()
assert src.isascii(), "the source must stay pure ASCII for pdfLaTeX on arXiv"
EOF
tar -czf arxiv-upload.tar.gz "$name.tex" "$name.bbl" references.bib
echo "wrote $name.pdf and arxiv-upload.tar.gz"
tar -tzf arxiv-upload.tar.gz
