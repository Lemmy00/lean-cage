# AR-tooling: Keep development reproducible and project-local

To serve [§GOAL-reuse](../goals.md#goal-reuse-extend-milestones-without-discarding-their-foundations) and [§FS-assurance.updates](../functional-spec/FS-assurance.md#updates-evidence-expires-with-its-dependencies), pin the proof environment and use
Grund to connect requirements, specifications, architecture, decisions, and tests.
This tool trial applies only to LeanCage.

## pins: Foundation dependencies and references

| Component | Pin | Role |
|---|---|---|
| Lean | `leanprover/lean4:v4.35.0` | Proof toolchain in `lean-toolchain` |
| Velvet | `836ed5a163b36c09081ed1d8aeecd3cec040f87e` | Lake dependency |
| Plausible | `dfa4f38190d07c37e315953e08b90fe2d95b3c24` | Transitive dependency locked in `lake-manifest.json` |
| Grund | `0.20.0` | Project-local documentation checker |
| Bubblewrap | `v0.13.1 / 362936aea0d5c6e70f7af75d2d44b5a914cb4ba2` | Behavioral reference; not installed by M0 |
| Linux | `6.18.59` | Initial integration reference; not installed by M0 |

Commit `lake-manifest.json` so transitive dependencies remain fixed. Pin changes
are deliberate reviewed changes, not an incidental consequence of development.
seLe4n is not a dependency of the Linux foundation.

## grund: Local wrapper and citation scope

Run `./scripts/grund.sh`, which downloads an upstream release only when its local
binary is missing, verifies the archive SHA-256, and installs under ignored
`.tools/`. It checks the cached tool's version on invocation. It does not change
global installations, editor configuration, or instructions for other projects.

The wrapper pins the GNU/Linux archive checksums:

| Architecture | SHA-256 |
|---|---|
| x86_64 | `2188f5d8c472a5e0a8db07982d60d2d8b18c8dfdf7e71a72125b407c14909d97` |
| aarch64 | `7d6c3f9f418eb97b4bab3635ceb460d13953e439f4d874d0a71f740710a8f04c` |

Use readable slug IDs, marked citations, named sections, and GitHub links.
Custom Lean support scans `--` comments. Put citations on ordinary standalone
line comments; do not rely on nested block comments or string parsing. Markdown,
Lean, shell, and Python are in scope; dependency/cache directories are excluded.
Extend and validate this configuration when adding a language.

## checks: One development gate

`./scripts/check.sh` runs configuration validation, managed-guidance consistency,
ordinary and full Grund checks, formatting checks, the citation-integration tests,
and `lake build`. Tests verify that Lean citations are actually discovered, a
dangling citation fails, and excluded dependency sources do not pollute the scan.

The library treats Lean warnings as errors. Security proofs additionally require
the statement/axiom review in [§AR-verification.audit](AR-verification.md#audit-statements-axioms-and-nonvacuity). These checks do not run hostile
guests, change the host, or certify any runtime security claim.

## maintenance: Generated guidance and section identities

Edit project rules outside Grund's managed block. After changing `grund.toml`,
run `./scripts/grund.sh init`. After editing citations, run
`./scripts/grund.sh fmt --write`, inspect the changes, and retain generated
section locks if any. Before renaming IDs, use `refs` to find their dependents.
Resolve stale IDs instead of excluding inconvenient files from checks.

The source of the setup conventions is the pinned
[Grund setup guide](https://github.com/agent-grounds/grund/blob/v0.20.0/crates/grund-core/assets/skills/grund-init/SKILL.md).
Grund's structural checks supplement Lean and tests; they do not validate proof truth.
