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
| Linux | `6.18.59 / 1253a6aa5d104312bf0992afacc15220ae35bdf9` | Disposable VM reference; never installed as the host kernel |
| QEMU / SeaBIOS | `8.2.2 / 1.16.3` | Checksum-pinned local Ubuntu packages in `tests/vm/bootstrap-pins.json` |

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
Lean, shell, Python, and C are in scope; dependency/cache directories are excluded.
Extend and validate this configuration when adding a language.

## checks: One development gate

Select checks by their inputs and the changed behavior. During implementation,
run the focused check that answers the current question. At a code/proof handoff,
run the foundation and affected package gates once on the final relevant inputs.
When an aggregate includes a prerequisite, count that run; do not run the
prerequisite again separately. Reuse a recorded pass with matching source,
dependencies and toolchain. Re-run after a relevant change or failure, for a newly
identified risk, or for an explicitly required independent replay. A new commit,
agent or handoff alone does not invalidate a result.

The reporting aggregate's reuse path first runs
`python3 scripts/check_foundation_inputs.py`. It compares the current foundation
source inventories with all three reviewed manifests and names any mismatch;
it neither builds proofs nor updates expectations. Matching helper bytes alone
cannot establish that the foundation's inputs still match. CI continues to run
the full foundation gate. Tests that consume a dependent Lean package build that
package explicitly, so they also work on a clean checkout.

For prose/workflow-only changes, run `grund fmt --write`, `grund check --full`,
`grund fmt --check` through the local wrapper, and `git diff --check`. Check any
affected documentation fingerprints without rebuilding unchanged proofs. A change
to a theorem contract, assurance claim, build input or tool configuration requires
the corresponding focused checks. This distinction applies to the command lists
in historical handoffs as well as current work.

Review changed statements and code, resolve findings, then finish the assignment.
Re-review the affected changes when resolving a finding; do not repeatedly review
unchanged work. Add tests for meaningful behavioral risks, not to mirror code or
produce another passing count. Required kernel checking and statement/assumption
audits remain part of accepting a new proof result.

`./scripts/check.sh` runs configuration validation, managed-guidance consistency,
ordinary and full Grund checks, formatting checks, then
`python3 scripts/audit_axioms.py` (including `lake build`), Python integration
tests, `lake env lean tests/integration/FilterContract.lean`, and
`lake env lean tests/integration/FilterDecoder.lean`.
The gate also compiles `lake build leancage-m1`, validates the archived
source-bound VM transcript via `python3 scripts/run_m1_vm.py --check-evidence`,
and runs `lake env lean tests/integration/Launch.lean`.
Documentation tests verify that Lean citations are actually discovered, a
dangling citation fails, C citations are discovered/rejected, and excluded
dependency sources do not pollute the scan.
The reference check interprets the filter on 14 architecture/syscall inputs under
[§AR-filter-slice.contracts](AR-filter-slice.md#contracts-lean-declarations-and-downstream-ownership). The decoder's 21 guard commands cover canonical, malformed,
ABI, boundary, and exhaustive single-byte substitution cases. Audit regressions
exercise actual forbidden transitive axioms under [§AR-filter-decoder.checks](AR-filter-decoder.md#checks-malformed-inputs-and-audit-failures).
The evidence report remains in ignored `.tools/`; nothing installs a guest filter.

The native target requires Linux x86-64, a C compiler and Linux headers. Lake uses
`lakefile.lean` for the explicit native static-library/executable build; Lean
options and dependency pins from the previous TOML build remain unchanged.
Native compilation executes no guest workload. The VM bootstrap is a separate
focused check: `python3 scripts/run_m1_vm.py --prepare` on Ubuntu 24.04 x86-64,
then `python3 scripts/run_m1_vm.py` for later replays. It uses cached,
checksum-pinned downloads without host package installation, privileged host
commands, KVM, host mounts, networking, or host seccomp experiments.
[§AR-m1-launch.vm](AR-m1-launch.md#vm-disposable-linux-profile-and-evidence) defines the recorded test profile.

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
