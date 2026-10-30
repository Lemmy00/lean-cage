#!/usr/bin/env bash
set -euo pipefail
# §AR-tooling.grund: Keep this experiment local to the repository.

project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
grund_version=0.20.0

case "$(uname -s)/$(uname -m)" in
  Linux/x86_64)
    grund_target=x86_64-unknown-linux-gnu
    grund_sha256=2188f5d8c472a5e0a8db07982d60d2d8b18c8dfdf7e71a72125b407c14909d97
    ;;
  Linux/aarch64)
    grund_target=aarch64-unknown-linux-gnu
    grund_sha256=7d6c3f9f418eb97b4bab3635ceb460d13953e439f4d874d0a71f740710a8f04c
    ;;
  *)
    printf '%s\n' 'The project Grund wrapper supports GNU/Linux x86_64 and aarch64.' >&2
    exit 1
    ;;
esac

grund_dir="$project_root/.tools/grund/$grund_version/$grund_target"
grund_bin="$grund_dir/grund"
if [[ ! -x "$grund_bin" ]]; then
  mkdir -p -- "$grund_dir"
  grund_tmp="$(mktemp -d "$grund_dir/.install.XXXXXXXX")"
  trap 'rm -rf -- "$grund_tmp"' EXIT
  grund_archive="grund-$grund_version-$grund_target"
  curl --fail --location --silent --show-error --retry 3 \
    "https://github.com/agent-grounds/grund/releases/download/v$grund_version/$grund_archive.tar.gz" \
    --output "$grund_tmp/release.tar.gz"
  printf '%s  %s\n' "$grund_sha256" "$grund_tmp/release.tar.gz" | sha256sum --check >&2
  tar -xzf "$grund_tmp/release.tar.gz" -C "$grund_tmp" "$grund_archive/grund"
  install -m 0755 "$grund_tmp/$grund_archive/grund" "$grund_tmp/grund"
  mv -f -- "$grund_tmp/grund" "$grund_bin"
  rm -rf -- "$grund_tmp"
  trap - EXIT
fi

if [[ "$("$grund_bin" --version)" != "grund $grund_version" ]]; then
  printf '%s\n' "Unexpected Grund version in $grund_bin; restore the pinned local tool." >&2
  exit 1
fi
cd -- "$project_root"
exec "$grund_bin" "$@"
