#!/usr/bin/env bash
set -euo pipefail
# §AR-m4-effects.gate: Replay maintained source/tools before the additive effect proofs.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
timeout 300 python3 m4/check.py
# §AR-m4-wire.evidence: Bound the expanded complete 212-module audit.
timeout 900 python3 m4/connection/check.py
