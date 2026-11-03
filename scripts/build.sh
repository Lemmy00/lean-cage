#!/usr/bin/env bash
set -euo pipefail
# §AR-workspace-vm.bundle: One root recipe stages the actual execution bundle.
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export PYTHONPATH="$project_root/python${PYTHONPATH:+:$PYTHONPATH}"
exec python3 -m leancage.build "$@"
