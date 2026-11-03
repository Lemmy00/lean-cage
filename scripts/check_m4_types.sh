#!/usr/bin/env bash
set -euo pipefail
# §AR-m4-routes.reporting.types: Replay checked representations and the actual type bijection.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
python3 -m unittest discover -s m4/types-bridge -p 'test_*.py' -v
python3 m4/types-bridge/check.py
