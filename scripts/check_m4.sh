#!/usr/bin/env bash
set -euo pipefail
# §AR-m4-native.evidence: Bounded replay; no implicit downloads or expectation regeneration.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
if [[ ! -x .tools/m4/CompCert/clightgen ]]; then
    echo 'Missing local M4 tools: run python3 m4/bootstrap.py after reviewing m4/LICENSES.md' >&2
    exit 1
fi
timeout 300 python3 m4/check.py
