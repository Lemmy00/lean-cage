#!/usr/bin/env bash
set -euo pipefail
# §AR-entry.acceptance: Check the integrated admission, preserved product and final VM receipts.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
./scripts/check_product.sh
python3 scripts/audit_entry.py
python3 verification/launch/native.py
./scripts/check_reporting.sh
python3 -m unittest discover -s verification/reporting -p 'test_identifiers.py' -v
python3 tests/product/acceptance.py --check-evidence
git diff --check
