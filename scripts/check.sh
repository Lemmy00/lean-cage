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
