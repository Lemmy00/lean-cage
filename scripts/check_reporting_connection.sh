#!/usr/bin/env bash
set -euo pipefail
# §AR-reporting.proof: Check the actual source/ordinary-Lean call interface.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
python3 verification/reporting/connection.py "$@"
