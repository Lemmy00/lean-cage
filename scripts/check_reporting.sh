#!/usr/bin/env bash
set -euo pipefail
# §AR-workspace.transport: Check the live collector, decoder and report publisher together.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
python3 verification/reporting/check.py "$@"
python3 -m unittest discover -s tests/integration -p 'test_output_capture.py' -v
python3 scripts/run_m3_vm.py --check-artifacts
