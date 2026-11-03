#!/usr/bin/env bash
set -euo pipefail
# §AR-m4-parent.audit: Replay the implemented chain, explicit amendments and parent repair.
# §REQ-proof-integrity.provenance: Passing this gate does not complete the open M4 obligations.

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"

run_check() {
  printf '\nChecking:'
  printf ' %s' "$@"
  printf '\n'
  "$@"
}

# §AR-workspace.transport: The corrected helper has a separately checked source binding.
if python3 verification/reporting/check.py --current-profile; then
  run_check ./scripts/grund.sh check --full .
  run_check ./scripts/grund.sh fmt --check
  run_check ./scripts/check_reporting.sh
  printf '\nCurrent reporting path and affected source consumers checked; unchanged evidence reused.\n'
  exit 0
fi
run_check ./scripts/check.sh
# The connection wrapper includes the original M4.1 gate.
run_check ./scripts/check_m4_connection.sh
for package in bridge controller plan main policy arguments digest validation initialization; do
  run_check python3 "m4/$package/check.py"
done
run_check python3 m4/parent/amendment.py --replay-candidate
run_check python3 m4/review/check_receipts.py
run_check python3 -m unittest discover -s m4/review -p 'test_*.py' -v
run_check python3 m4/parent/check.py
# §AR-m4-routes.evidence: Reproduce failed central connections without weakening their goals.
run_check python3 m4/routes/check.py
# §AR-m4-routes.reporting.types: Check the recursive representations and native type relation.
run_check ./scripts/check_m4_types.sh
run_check python3 scripts/run_m3_vm.py --check-artifacts

printf '\nImplemented M4 checkpoints, parent contract, connection attempts and type bridge replayed.\n'
printf 'The original correspondence obligations remain open. No VM workloads were run.\n'
