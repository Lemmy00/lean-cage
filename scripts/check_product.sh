#!/usr/bin/env bash
set -euo pipefail
# §AR-tooling.checks: The affected product gate includes the foundation exactly once.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
python3 scripts/rebind_product_evidence.py
./scripts/check.sh
python3 scripts/audit_product.py
python3 -m unittest discover -s tests/product -p 'test_*.py' -v
cc -std=c11 -O2 -Wall -Wextra -Werror -static -no-pie linux/vm_init.c \
  -o .tools/assurance/workspace-vm-init
