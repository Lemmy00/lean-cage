#!/usr/bin/env bash
set -euo pipefail
# §AR-compiled-reporting.certificate: Reuse checked source/compiler/decoder evidence.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
python3 verification/compiler/check.py "$@"
