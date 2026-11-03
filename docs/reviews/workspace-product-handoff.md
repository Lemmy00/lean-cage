# Reusable Linux workspace product handoff — 2026-11-03

M4 is complete for [§FS-linux-product.acceptance](../functional-spec/FS-linux-product.md#acceptance-product-completion). A developer or agent can build
from the root, supply a supported policy and private inputs, execute Python or
shell in an owned disposable VM, and retrieve that request's report, captures
and regular-file exports. The CLI and libraries use the maintained core rather
than a parallel milestone implementation. Implementation commit: `506337e`.

## Working public workflow

```sh
./scripts/build.sh
./leancage check examples/workspace/python-policy.json \
  --workspace examples/workspace/input --stdin examples/workspace/stdin.txt
./leancage run examples/workspace/python-policy.json \
  --workspace examples/workspace/input --stdin examples/workspace/stdin.txt
./leancage report REQUEST_ID
```

Python exports `summary.json` containing `{"stdin": "caller stdin", "sum": 42}`.
The shell policy in the same directory exports `answer.txt` with the caller's
message and stdin. Both return separate stdout/stderr. The examples are ordinary
caller requests; the programs themselves arrive through the private input snapshot.
The [running guide](../running.md) covers policy changes, storage, cancellation,
exit statuses, selected bundles and reusable integrations.

`python/leancage/runner.py:Workspace` is the shared host API (`check`, `run`,
`report`, plus `Cancellation`). The root CLI imports it. The staged
`bundle/bin/leancage` and `bundle/python` work through the same implementation;
acceptance exercises the staged shell workflow. `library/LeanCageWorkspace.lean`
exposes the typed `LeanCage.Workspace` interface. Its execution guard validates
typed policy values before invoking the existing controller/helper path.

## Components, ownership and exact artifacts

`scripts/build.sh` stages `.tools/product/bundle/manifest.json`. That manifest
identifies the actual controller/helper, VM init, filter, frozen runtime,
kernel/configuration, local emulator/firmware closure, compiler/runtime versions,
source hashes, checked Lean artifacts and proof records. It enumerates native,
VM and host application adapters separately from logical proofs. The exact tested
bundle identity is in `assurance/product-vm-evidence.json`.

Canonical implementation homes and compatibility aliases are in
`assurance/product-layout.json` and [§AR-workspace-vm.migration](../architecture/AR-workspace-vm.md#migration-preserve-proof-identities-while-moving-maintained-components). Old `m2`, `m3`,
native/profile/runtime-script paths are symlinks to maintained functional homes.
Existing Lean declaration/import names and private ABI names preserve exact
proof terms and receipts. No implementation copies were introduced. Historical
proof snapshots remain reproducible at their recorded revisions.

The host owns one QEMU process group/socket per request. VM init owns the
controller. Its second UART carries trusted framing; boot text and workload
output have separate channels. Requests and responses bind a fresh request ID
to the bundle. Snapshots and exports have descriptor/path/type/byte/inode/depth
checks; exported names are validated before writing into a fresh private host
directory. Publication cannot replace another run's directory.

Cancellation uses parent/executable checks and pidfds to reach the helper after
its signal handling is armed. Process lookup uses the supported `/proc` status
interface, since the pinned kernel omits `CONFIG_PROC_CHILDREN`. Channel loss or
timeout never manufactures entry or inner cleanup. Already received observations
survive later transport/storage failures. VM teardown and observed helper cleanup
are separate fields. These contracts are [§AR-workspace-vm.request](../architecture/AR-workspace-vm.md#request-freeze-bounded-caller-inputs-before-boot),
[§AR-workspace-vm.channel](../architecture/AR-workspace-vm.md#channel-separate-trusted-framing-from-guest-output) and [§AR-workspace-vm.lifetime](../architecture/AR-workspace-vm.md#lifetime-cancellation-loss-and-publication).

## Checked core and assurance boundary

Full statements, hypotheses, transitive axioms and sources are in
`assurance/product-core.json`; actual consumers are recorded beside them.

| Property | Actual executable definition and checked evidence |
|---|---|
| Policy validation and bounds | `decodePolicy`, `validatePolicy`, `validatePolicy_iff`, `decodePolicy_iff`, `decodePolicy_bounds`; the bundled controller validates the host's exact frozen policy |
| Typed library admission | `LeanCage.Workspace.execute`, `accepted_policy_executes`, `rejected_policy_is_pure`, `supported_policy_inhabited`; valid policies use the same `invoke`, invalid bounds return a pure error |
| Filter decisions | `Filter.policy_filter_action` quantifies over architecture/syscall/clone words; build/audit compares every emitted byte with the native header |
| Result validation | The actual `API.invoke` calls `decodeResult`; `decodeResult_valid` preserves concrete knowledge/bounds checks |
| JSON publication observations | `publication_entry` and `publication_cleanup` quantify over arbitrary result, policy, identity, status and storage error and preserve the original fields |
| Conditional native reporting connection | Preserved `LeanCage.Reporting.live_publication`, source sender and compiler declarations remain at their exact owned-input/runtime/caller premises |

The ordinary Lean kernel checked the new terms. Only recorded subsets of
`propext`, `Classical.choice`, `Quot.sound` occur; forbidden axioms are rejected.
No earlier theorem type or axiom set changed. The policy witness and real allowed
workflows establish nonvacuity at their respective logical/test boundaries.

The Linux, compiler/runtime/FFI, hardware/VM and enumerated application-adapter
trust is [§FS-linux-product.trust](../functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product). The host transport and complete native
authority/supervision path have tests and explicit adapter contracts, not whole
source correspondence proofs. Complete application verification is M5; selected
platform and hardware-channel improvements are M6. The historical correspondence
ledger and its scope fields remain unchanged.

## Validation and preservation

| Check | Result |
|---|---|
| Root build | Passed; actual execution bundle staged with pinned assets |
| Foundation through `scripts/check_product.sh` | Passed: 79 Python tests, 168 Lean guards, native compilation, source/evidence checks; original 445/274/419 theorem inventories preserved |
| Product core audit | Passed: exact types/axioms/source bindings for the shipped core and typed public interface |
| Final product boundary tests | Passed: 17 tests, including replay of the exact historical metadata preimage and rejection of theorem/axiom/scope/cache changes |
| Reporting/compiler aggregate | Passed with matching proof artifacts reused; live capture regression and retained 60-case/3-API/6-boundary VM artifact checks passed |
| Public caller VM suite | Passed: 12 scenarios through the root/staged interfaces and shared library, including denial, cancellation, storage failure and channel/VM loss |
| Documentation/fingerprints/whitespace | Passed; status-only changes reuse unchanged proof/runtime evidence |

The foundation and product checks were selected by affected inputs under
[§AR-tooling.checks](../architecture/AR-tooling.md#checks-one-development-gate). The extra metadata regression and final status updates use
their focused checks. The final bundle's identity and test/source hashes are in
`assurance/product-vm-evidence.json`; local returned artifacts remain under
`.tools/product/acceptance/BUNDLE_ID/`. Logs are under `.tools/assurance/`:
`product-handoff-check.log`, `product-reporting-check.log` and
`product-acceptance.log`.

`assurance/product-validation.json` records the exact commands, exits, bundle/core
identities and retained log hashes for the completed handoff.

`assurance/product-evidence-migration.json` preserves the original receipt hashes
and freezes their theorem/axiom/scope/source/cache payloads. Only the status
document, dependent fingerprint fields and the explicitly identified operational
metadata adapter change. The adapter composes the previous checked preimage with
that bounded amendment; it does not regenerate proof expectations. Normal gates
only check this record. Deliberate status-document maintenance uses
`scripts/rebind_product_evidence.py --apply`, followed by fingerprint/Grund checks.

The next concrete work is the first region of [§RM-roadmap.m5](../roadmap.md#m5-verify-the-complete-application-control-path): connect the actual
validated policy/input bytes through setup to guest admission against primitive
Linux/runtime contracts, consuming this product and the accepted source/reporting
regions. It does not require rebuilding the product workflow or starting kernel
research.
