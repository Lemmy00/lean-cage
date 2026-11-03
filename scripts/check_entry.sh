#!/usr/bin/env bash
set -euo pipefail
# §AR-entry.acceptance: Check current partial entry work, without claiming complete admission.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
python3 scripts/rebind_product_evidence.py
python3 scripts/check_foundation_inputs.py
./scripts/grund.sh config validate .
./scripts/grund.sh init --check
./scripts/grund.sh check --full .
./scripts/grund.sh fmt --check
python3 scripts/audit_entry.py
python3 verification/launch/native.py
git diff --check
