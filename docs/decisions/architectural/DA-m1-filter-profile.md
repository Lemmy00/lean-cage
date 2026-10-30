# DA-m1-filter-profile: Fix the first filter and launch boundary

**Status: accepted for M1.** Use [§AR-filter-slice.contracts](../../architecture/AR-filter-slice.md#contracts-lean-declarations-and-downstream-ownership) for
[§FS-filter-loading.input.subset](../../functional-spec/FS-filter-loading.md#inputsubset-one-canonical-restrictive-filter) and [§FS-filter-loading.installation.effects](../../functional-spec/FS-filter-loading.md#installationeffects-os-effects-and-post-install-boundary).

## choice: Small native profile and explicit departures

Choose Linux x86-64 LP64 little-endian and one canonical nine-instruction filter.
Check the audit architecture, reject syscall words at or above the x32 marker,
deny direct `getppid` with `EPERM`, and permit other native words. This supplies
an observable denial and useful allowed actions without a policy compiler or
general BPF verifier. It establishes no broader isolation or confidentiality.

Use a finite byte snapshot, check bounds before narrowing, and reject every
noncanonical program. Unlike the pinned Bubblewrap path, do not accept arbitrary
filters, chain programs, or cast bytes into native structs. The M1.4 demo's
bounded file adapter closes its input before native entry under
[§AR-m1-launch.binding](../../architecture/AR-m1-launch.md#binding-small-native-boundary); hostile mutable-file ingestion remains a later obligation.

Use no-new-privileges and current-thread installation in a prepared trusted child,
followed by one direct `execve`. Omit Bubblewrap's post-install notification and
`execvp` behavior. [§AR-filter-slice.source](../../architecture/AR-filter-slice.md#source-pinned-bubblewrap-path) records these departures; tests must
not be presented as full Bubblewrap equivalence.

## consequences: Work package and trust boundary

M1.1 fixes source/ABI/state/effect/failure contracts and Lean vocabulary. M1.2 and
M1.3 implement the decoder and launch semantics after this boundary is reviewed.
M1.4 adds a binding and isolated demonstration. Linux, native executable,
entry-environment, and hardware gaps in [§FS-assurance.assumptions](../../functional-spec/FS-assurance.md#assumptions-initial-assumption-and-obligation-register) remain explicit.

## decoder: M1.2 proof and audit choices

Use checked byte indices and exact bounded unsigned word construction for
[§FS-filter-loading.input.layout](../../functional-spec/FS-filter-loading.md#inputlayout-serialized-instructions-and-bounds), with a mathematical layout predicate independent
of the decoder. Ordinary Lean proofs serve this pure slice under
[§AR-filter-decoder.proofs](../../architecture/AR-filter-decoder.md#proofs-independent-statement-and-useful-witnesses); Velvet remains available for later imperative work.

Audit the complete project theorem inventory, including generated support, while
separately identifying the authored decoder claims. Fix the permitted logical
axioms to `propext`, `Classical.choice`, and `Quot.sound`, and require each exact
reviewed axiom set and theorem type. The source-bound manifest and actual Lean
artifact report implement [§AR-filter-decoder.audit](../../architecture/AR-filter-decoder.md#audit-declaration-type-and-axiom-gate) for [§FS-assurance.decoder](../../functional-spec/FS-assurance.md#decoder-m12-decoder-claim-record);
they establish no native compiler/runtime or Linux correspondence.

## launch: M1.3–M1.5 model, native boundary, and replay choices

Use total stage/event transitions and finite replay under [§AR-m1-launch.model](../../architecture/AR-m1-launch.md#model-total-transitions-and-trace-evidence)
for [§FS-filter-loading.installation.model](../../functional-spec/FS-filter-loading.md#installationmodel-executable-launch-semantics-and-proof-obligations). Retain every documented failure,
interruption, cancellation and termination outcome. Prove exact successful
history as well as receipt membership; connect actual decoder results and keep
success/failure witnesses. Entry conditions and truthful OS effects are explicit
application premises, not extra Lean axioms or conclusions assumed by the proof.

For [§FS-filter-loading.installation.binding](../../functional-spec/FS-filter-loading.md#installationbinding-first-concrete-linux-driver), prepare fixed private C storage
before fork, then keep Lean/runtime/allocator calls out of the child. Use an
error-only close-on-exec pipe; successful installation proceeds directly to exec.
This extends the earlier no-notification choice with failure reporting without
adding a success notification. Link with `-Wl,-z,now` to avoid first-call PLT
resolution between installation and exec. Supervision errors remain distinct
from evidence that guest execution never occurred.

Migrate `lakefile.toml` to `lakefile.lean` to express the native object/static
library target and scoped executable. Preserve Lean options and exact
Velvet/Plausible pins; this is a build-definition format change, not a dependency
upgrade. Add the C comment reader to Grund and exercise its actual discovery and
rejection behavior. Original native/fixture code uses Apache-2.0, without
translating or copying Bubblewrap C code.

Use a dedicated project-local QEMU TCG VM rather than shared-host enforcement
experiments, per [§AR-m1-launch.vm](../../architecture/AR-m1-launch.md#vm-disposable-linux-profile-and-evidence). Build the exact Linux 6.18.59 reference from a
checksum-pinned archive, retain its full resolved configuration, and pin local
Ubuntu tool packages. A one-vCPU, 2048-MiB, NIC-free/disk-free ephemeral initramfs
accommodates Lean's startup stack reservation while keeping the experiment
bounded. VM configuration is experimental test infrastructure, not a resource
isolation or hardware-channel security claim.

Retain `assurance/filter-decoder.json` as the extended M1 declaration/type/axiom
manifest under [§AR-m1-launch.audit](../../architecture/AR-m1-launch.md#audit-preserve-decoder-claims-and-extend-the-assurance-gate). Preserve an independent original 18-claim
decoder baseline and review all new full types/axiom sets. Record raw and
structured VM evidence separately; source-bound archived evidence checks are
fast handoff checks, and explicit VM replays supply runtime observations.
