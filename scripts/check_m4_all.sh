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
run_check python3 scripts/run_m3_vm.py --check-artifacts

printf '\nImplemented M4 checkpoints and parent repair replayed; independent promotion review remains required.\n'
printf 'The original correspondence obligations remain open. No VM workloads were run.\n'
