#!/usr/bin/env bash
set -euo pipefail
# §AR-tooling.checks: One entrypoint checks documentation and the Lean foundation.

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
./scripts/grund.sh config validate .
./scripts/grund.sh init --check
./scripts/grund.sh check .
./scripts/grund.sh check --full .
./scripts/grund.sh fmt --check
python3 -m unittest discover -s tests/integration -p 'test_*.py' -v
lake build
