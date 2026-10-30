#!/usr/bin/env bash
set -euo pipefail
# §AR-tooling.checks: Check proofs, native compilation, archived VM evidence, and pure fixtures.

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
./scripts/grund.sh config validate .
./scripts/grund.sh init --check
./scripts/grund.sh check .
./scripts/grund.sh check --full .
./scripts/grund.sh fmt --check
python3 scripts/audit_axioms.py
lake build leancage-m1
python3 scripts/run_m1_vm.py --check-evidence
python3 -m unittest discover -s tests/integration -p 'test_*.py' -v
lake env lean tests/integration/FilterContract.lean
lake env lean tests/integration/FilterDecoder.lean
lake env lean tests/integration/Launch.lean
# §AR-lifecycle.audit: Compile the VM-only helper without running workloads on the host.
mkdir -p .tools/assurance
cc -std=c11 -O2 -Wall -Wextra -Werror -static -no-pie native/leancage_m2.c \
  -o .tools/assurance/leancage-m2-helper
python3 scripts/audit_m2.py
python3 -m unittest discover -s m2/tests/integration -p 'test_*.py' -v
(cd m2 && lake env lean tests/integration/Lifecycle.lean)
