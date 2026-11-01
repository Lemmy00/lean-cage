# FS-assurance: Bind every advertised guarantee to auditable evidence

To meet [§GOAL-end-to-end.outcome](../goals.md#outcome-auditable-claims), distinguish target contracts, model theorems,
tests, assumptions, and deployed guarantees. Grund validates document structure
and citations; it cannot determine whether a security claim is true.

## evidence: Required claim record

For each security claim record: stable specification ID; plain-language scope;
exact Lean declarations and their types; transitive axioms and hypotheses;
implementation/source revision; executable hashes; compiler/runtime/FFI versions;
kernel version, configuration and image identity; hardware profile; observation
model; assumptions; open obligations; and reproducible proof/test commands.
An absent field must say why it is absent. A citation is not a proof binding.

The M1 manifest (retaining the M1.2 filename) in `assurance/filter-decoder.json` checks named claims and the
complete project theorem inventory against actual types, transitive axioms, and
source/dependency fingerprints. Its report identifies checked Lean artifacts.
`assurance/m1.2-decoder-claims.json` preserves the 18 reviewed decoder statements
and their axiom sets independently of the extended inventory. Native artifact
certification remains an obligation; the separate VM record below is test evidence.

## status: Initial claim register

M1's handoff gate passed on 2026-10-30: 21 Python integration tests; 58 Lean
guards (14 reference, 21 decoder, 23 launch); native compilation; archived VM
evidence validation; and exact type/axiom checks of 43 authored claims within
445 total theorem declarations, with 39 source/dependency/evidence fingerprints.
All 18 original decoder claim types and axiom sets are preserved. The explicit
VM replay, including a fresh pinned source/kernel build, passed all 13 cases.
These counts identify coverage and evidence, not a measure of security strength.

| Claim | Contract | State | Present evidence | Missing connection |
|---|---|---|---|---|
| Validated authority | [§FS-workspace.authority](FS-workspace.md#authority-objects-and-rights) | Conditional model proofs; VM implementation | [§FS-assurance.workspace](FS-assurance.md#workspace-m3-workspace-model-and-vm-evidence); reachable issued handles and process inheritance | Native/VFS/loader correspondence and broader policies |
| Canonical filter decoding | [§FS-filter-loading.input.correctness](FS-filter-loading.md#inputcorrectness-decoder-proof-boundary) | Model-proved; pure executable checks | [§FS-assurance.decoder](FS-assurance.md#decoder-m12-decoder-claim-record); exact acceptance, bounds, rejection and nonvacuity proofs; axiom gate | Native executable and FFI field-copy correspondence |
| M1 fail-closed launch order | [§FS-filter-loading.installation.model](FS-filter-loading.md#installationmodel-executable-launch-semantics-and-proof-obligations) | Model-proved; VM-tested native slice | [§FS-assurance.launch](FS-assurance.md#launch-m13-launch-order-claim-record) and [§FS-assurance.demo](FS-assurance.md#demo-m14-isolated-linux-test-record); actual-decoder linkage, exact successful order, terminal failures, native call map and 13 VM cases | Native/source/compiler/runtime/FFI and Linux correspondence; broader M2 lifecycle |
| M2 owned lifecycle and filter action | [§FS-lifecycle.model](FS-lifecycle.md#model-executable-controller-and-effect-contracts) and [§FS-lifecycle.filter](FS-lifecycle.md#filter-general-action-of-the-preserved-m1-program) | Model-proved; VM-tested; handoff gate passed | [§FS-assurance.lifecycle](FS-assurance.md#lifecycle-m2-lifecycle-and-filter-semantics-claim-record); exact plan, ownership/inheritance and general bytecode action; source-bound VM evidence | Native/Linux correspondence; M3 authority; M5 hardware channels |
| Native workload confinement | [§FS-workspace.authority](FS-workspace.md#authority-objects-and-rights) | M3 model proofs, implementation and source-bound VM evidence; gate passed | [§FS-assurance.workspace](FS-assurance.md#workspace-m3-workspace-model-and-vm-evidence); object/handle/alias model and workspace helper | Native/Linux correspondence |
| Bounded resources | [§FS-workspace.resources](FS-workspace.md#resources-units-ownership-and-failure) | Conditional model proofs; native VM limit cases | Scope/capture/reservation/sample proofs; charged memory/task/CPU/deadline observations | Linux accounting and progress/overshoot premises |
| Local reporting source behavior | [§FS-workspace.results](FS-workspace.md#results-entry-cancellation-and-bounded-transport) | Partial M4.2 source/effect proofs | [§FS-assurance.native](FS-assurance.md#native-partial-m4-reporting-source-evidence); maintained-source codecs, write loop, errno, selectors, result construction, child-failure reporting and complete private-frame decoding | Whole-slice framing/caller safety, checked C-to-Lean bridge, Linux/compiler/executable correspondence |
| Functional confidentiality | [§FS-observations.logical](FS-observations.md#logical-functional-observations) | Planned | Observation requirements | Noninterference theorem and correspondence |
| Hardware-aware confidentiality | [§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) | Planned | Scope and research obligations | Model, mechanisms, proof, deployed profile |
| Deployed executable correctness | [§GOAL-end-to-end](../goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact) | Planned | Roadmap | Compiler/runtime/FFI and Linux correspondence |

M1 supplies decoder and launch transition proofs plus a runnable VM-only filter
driver. Its filter permits most syscalls and provides no full sandbox confinement.
There are no certified native executables or supported production profiles.
Model proofs, tested source mappings, Linux enforcement, and executable
correspondence remain separate evidence boundaries.

## decoder: M1.2 decoder claim record

**Scope:** [§FS-filter-loading.input.correctness](FS-filter-loading.md#inputcorrectness-decoder-proof-boundary), [§FS-filter-loading.input.layout](FS-filter-loading.md#inputlayout-serialized-instructions-and-bounds),
and [§FS-filter-loading.input.errors](FS-filter-loading.md#inputerrors-deterministic-rejection-and-decoder-interface). For every ABI descriptor and finite byte
snapshot, `decode` succeeds exactly for the specified native ABI and mathematical
72-byte canonical layout. Success implies safe byte indices and an unchanged
16-bit instruction count. Validation errors retain the specified precedence and
first differing instruction. A concrete snapshot succeeds. This proves no launch,
Linux enforcement, native layout, isolation, or confidentiality property.

All following names are in namespace `LeanCage.Linux.Filter`; their full types,
implicit hypotheses, and exact per-declaration axiom sets are recorded in
`assurance/filter-decoder.json` and compared to the actual Lean environment.

| Declarations | Reviewed proposition |
|---|---|
| `decodeU16LE_toNat`, `decodeU32LE_toNat` | For all byte values, unsigned word reconstruction equals the specified mathematical sum |
| `readInstruction_eq_iff` | For an actually bounded eight-byte region, decoded instruction equality is equivalent to the independent byte-layout equations |
| `firstMismatch_eq_none_iff`, `firstMismatch_eq_some_iff` | The scan accepts exactly all matching layouts or identifies the first differing layout |
| `decode_success`, `decode_complete`, `decode_ok_iff` | For every ABI/snapshot/program, decoder success is equivalent to `ValidInput`; no validity premise is assumed for soundness |
| `decode_bounds` | A successful result implies 72 bytes, count at most 4096 and 65535, exact `UInt16` narrowing, and all instruction/field indices in bounds |
| `decode_unsupported_abi`, `decode_empty`, `decode_oversized`, `decode_misaligned`, `decode_unsupported_length` | The documented preceding checks and current rejection condition imply the exact error, before field reads |
| `decode_rejects_invalid` | Every snapshot/ABI outside `ValidInput` returns an error |
| `decode_at_valid_size`, `decode_mismatch_iff` | Native ABI and checked 72-byte size expose exactly the first field-layout mismatch |
| `decode_canonical` | The explicit 72-byte `canonicalBytes` succeeds; kernel reduction checks this nonvacuity witness |

`InstructionLayout` states bounded byte reads and numerical field equations;
`ValidInput` states native ABI, exact size, and all nine layouts. Neither calls
the decoder or assumes its result. The definitions and total Lean decoder are in
`LeanCage/Proofs/FilterDecoder.lean` and `LeanCage/Linux/FilterDecoder.lean`.
Termination here follows from total Lean definitions and a bounded finite scan;
there is no OS liveness or successful guest-execution claim.

**Axioms and hypotheses:** the audited union is `propext`, `Classical.choice`,
and `Quot.sound`; the manifest records the smaller set for each declaration.
These are explicitly accepted logical foundations under [§REQ-proof-integrity.kernel](../requirements/REQ-proof-integrity.md#kernel-kernel-checked-evidence),
not OS assumptions. All other axioms, including `sorryAx` and compiler-trust
axioms, are rejected even if inserted into the expected manifest. Bounds and
validation hypotheses are visible in the full theorem types. No Linux, FFI,
hardware, observer, or privilege premise supports these decoder results.

**Source and artifact identities:** these are local working-tree results, not a
published or committed release. The manifest pins each project Lean source, audit
source, normative decoder/proof/evidence contracts, `lean-toolchain`,
`lakefile.lean`, and `lake-manifest.json` by SHA-256. The Lake configuration changed
format to build the native driver; dependency revisions did not change.
The reproducible audit builds with Lean `v4.35.0`, checks actual declaration/type/
axiom evidence, and writes `.tools/assurance/filter-decoder-report.json` with the
checker version and hashes of checked `.olean` artifacts and their private/server
companions where present. Upstream references and dependency revisions are
unchanged. These identities bind this check to source and Lean artifacts, not
to a certified native sandbox executable.

**Validation:** run `./scripts/check.sh`, or `python3 scripts/audit_axioms.py`
for build plus theorem audit. Pure fixture checks are
`lake env lean tests/integration/FilterContract.lean` and
`lake env lean tests/integration/FilterDecoder.lean` after building. The decoder
suite has 21 guard commands, covering all 72 truncated prefixes, eight extra
lengths, size/count boundaries, ABI/error precedence, and all 18360 single-byte
substitutions. The original 14 reference-filter checks remain. Python integration
tests exercise missing/changed declarations, source drift, and actual transitive
custom, `sorryAx`, and native-compiler axioms in disposable fixtures.

**Deployment boundary and remaining obligations:** native/kernel/hardware fields
do not apply to this pure theorem; the separate demonstration in [§FS-assurance.demo](FS-assurance.md#demo-m14-isolated-linux-test-record)
records them for its own scope. [§FS-assurance.assumptions](FS-assurance.md#assumptions-initial-assumption-and-obligation-register) retains faithful checking (A-logic), native
compiler/runtime/FFI correspondence (A-executable), and later model/platform/
enforcement obligations. ABI descriptors are input metadata, not measurements of
the host or guest. The launch and demonstration records below add those M1
results without strengthening this decoder theorem. The hardware destination in
[§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) remains open and unchanged.

## launch: M1.3 launch-order claim record

**Scope:** [§FS-filter-loading.installation.model](FS-filter-loading.md#installationmodel-executable-launch-semantics-and-proof-obligations) and
[§FS-filter-loading.installation.failure](FS-filter-loading.md#installationfailure-terminal-failures-without-rollback-claims). For every finite reachable trace,
an exec attempt follows validation, no-new-privileges, and installation;
successful image replacement has exactly that order followed by the exec attempt
and success event. No event leaves failure or termination. Arbitrary invalid
inputs cannot reach image replacement through the actual decoder verdict.

The exact full types and transitive axiom sets of all 25 new authored theorems
are recorded in `assurance/filter-decoder.json`. Names below use
`LeanCage.Launch` unless explicitly qualified.

| Declarations | Reviewed proposition |
|---|---|
| `failed_terminal`, `terminated_terminal` | For either verdict and every possible event, the terminal state has no outgoing transition |
| `step_receipts`, `reaches_receipts` | Every transition/reachable state preserves the receipts required for its successful stage |
| `step_validation_guard`, `reaches_validation_guard` | Successful setup states require a positive validation verdict |
| `validation_before_no_new_privileges`, `no_new_privileges_before_install`, `install_before_exec`, `install_before_guest` | Each reachable setup/exec success event has the specified earlier receipts in its preceding history |
| `step_successful_history`, `reaches_successful_history`, `executed_trace_exact` | Successful states have their exact ordered histories; every executed trace is `successTrace` |
| `replay_append`, `reaches_replay`, `replay_extends_reaches`, `replay_iff_reaches` | Executable finite replay and inductive reachability describe the same transitions from the initial state |
| `rejected_never_executes` | For any trace, false validation excludes image replacement |
| `success_witness`, `failed_install_witness`, `interrupted_install_witness` | Concrete success, errno-22 installation failure, and interrupted installation traces are inhabited |
| `LeanCage.Linux.validationVerdict_iff` | Actual decoder acceptance together with the entry-check flag is equivalent to the independent input predicate and a true flag |
| `LeanCage.Linux.invalid_input_never_executes` | For every ABI, snapshot, entry flag and trace, invalid input excludes image replacement |
| `LeanCage.Linux.prepared_filter_valid` | Every typed native input carries an actual decoding receipt and satisfies the mathematical byte specification |
| `LeanCage.Linux.decoded_success_witness` | The actual canonical snapshot and full successful launch trace are jointly inhabited |

**Model and premises:** `Model.lean` defines actual stage/event transitions,
`Reaches` starts at `unvalidated`, and `replay` is total on finite traces. Failure
and external termination can occur during setup; ordinary errors, interruption,
effective cancellation, and unexpected binding returns are distinct outcomes.
Terminal states do not assert rollback. This is partial correctness, not process
termination, OS liveness, or universal syscall success. The success witnesses
are kernel reductions under concrete bytes and a true entry flag; they do not
assume the desired launch invariant as a hypothesis.

**Logical foundations:** launch-only theorems use subsets of `propext` and
`Quot.sound`; the decoder-linked theorems additionally use `Classical.choice`.
Their exact sets are audited; no new OS axiom or opaque foreign-function axiom
supports these proofs. `nativeLaunch` has a safe failing Lean fallback and a
native override. The theorem gate does not prove that override correct.

**Connection to execution:** truthful success/failure observations, persistence
of no-new-privileges/filter through exec, and the entry conditions in
[§FS-filter-loading.installation.entry](FS-filter-loading.md#installationentry-entry-conditions-and-interference) are environmental premises of applying the
model to a real process. The [native call map](../architecture/AR-m1-launch.md#binding-small-native-boundary) identifies the concrete implementation.
Native C, compiler/runtime/FFI, Linux, loader, file stability, and platform
correspondence remain A-model/A-entry/A-executable/A-linux/A-platform obligations.
No hostile transition allowed by the stated entry profile is removed; hostile
mutation outside that profile remains an explicit M2–M4 obligation.

**Identities and validation:** these are local working-tree results with
SHA-256-bound Lean/native/test/contracts in the reviewed manifest, not a release.
`python3 scripts/audit_axioms.py` rebuilds and checks the full project inventory
and records checked `.olean` identities in
`.tools/assurance/filter-decoder-report.json`. Run `./scripts/check.sh` for the
handoff gate and `lake env lean tests/integration/Launch.lean` for executable
trace guards. Native image/platform fields belong to the following test record;
the proof's observation model is public functional launch events only.

## demo: M1.4 isolated Linux test record

**Evidence:** `assurance/m1-vm-evidence.json` and the complete raw
`assurance/m1-vm-transcript.log` record 13 passing cases, including a fresh
checksum-pinned Linux source build. The record identifies every relevant source,
kernel image/configuration, initramfs file, compiled driver/guest, runtime,
QEMU/TCG and firmware artifact, with the exact command and environment.
This is functional test evidence for [§FS-filter-loading.installation.binding](FS-filter-loading.md#installationbinding-first-concrete-linux-driver)
and [§FS-filter-loading.claim](FS-filter-loading.md#claim-limited-first-theorem), not a native correspondence proof.

| Case group | Observed result |
|---|---|
| Allowed and denied native syscalls | Direct `getpid` positive; direct `getppid` raw `-1` (`-EPERM`); no-new-privileges 1; seccomp mode 2; UID 65534; guest exits 0 |
| Empty, truncated, permissive, oversized, byte-swapped filters | Exact decoder diagnostic and exit 64; no guest marker |
| Non-ELF target | Preflight `ENOEXEC` (8), exit 125; no guest marker |
| No-new-privileges and installation errors | Actual invalid-argument calls return `EINVAL` (22) at the correct phase with earlier receipt bits; exit 125, no guest marker |
| Exec error | Trusted static ELF without executable permissions returns `EACCES` (13) after installation; exit 125, no guest marker |
| Terminated setup | Actual SIGTERM before restriction, diagnostic signal 15, launcher exit 143, no guest marker |
| Unsupported x32/i386 syscall ABI | Guest first checks ordinary allowed/denied actions; then SIGSYS (31), launcher exit 159 |

**Recorded environment:** Linux 6.18.59 commit
`1253a6aa5d104312bf0992afacc15220ae35bdf9`; native x86-64 LP64 little-endian;
one QEMU 8.2.2 TCG `max` vCPU and 2048 MiB RAM; SeaBIOS 1.16.3; no NIC, host
mount, or persistent disk. PID 1 is trusted root; launcher/guest use UID/GID
65534 with no supplementary groups. Lean 4.35.0 and the actual C compiler/libc
versions are recorded. Lean's startup event-loop thread reserves 1 GiB virtual
stack; the main-thread stack is configured to 8192 KiB. This is not a workload
resource-limit claim. The virtual CPU reports QEMU TCG CPU version 2.5+ and
virtual microcode `0x1000065`; physical CPU/microcode verification is absent
because this test makes no physical hardware claim.

**Replay and gate:** on the recorded Ubuntu 24.04 x86-64 development host, run
`python3 scripts/run_m1_vm.py --prepare`. It downloads only checksum-pinned
packages into `.tools/`, extracts them without host installation, builds a fresh
kernel, compiles the trusted fixture, and boots an ephemeral initramfs. Further
replays can omit `--prepare`. The kernel has no dependency on the shared host's
kernel or KVM. A 180-second timeout and strict transcript verifier reject missing
cases, infrastructure failures, wrong errno/receipt values, and guest execution
in rejected cases. The final gate checks archived source/transcript identities
with `--check-evidence`; it explicitly does not rerun the VM or certify a newly
compiled binary. Source changes require an explicit fresh VM run.

**Open assumptions and absent guarantees:** C/Lean compilation, runtime, FFI,
ELF loading, native buffer/call mapping, Linux seccomp, trusted entry and stable
files, firmware/emulator correctness, and physical hardware remain unproved.
The C source and VM fixture are original Apache-2.0 code; the pinned Bubblewrap
source is reference material, not copied code. Linux and locally extracted tools
retain upstream licensing; their binaries are not committed. This M1 record does
not establish the separate M2 lifecycle in [§FS-assurance.lifecycle](FS-assurance.md#lifecycle-m2-lifecycle-and-filter-semantics-claim-record). Native
descriptor/alias/adversarial interference and BPF/kernel refinement, and full
isolation/confidentiality guarantees remain open. Timing/cache/contention/
speculation observations in [§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) are outside this test;
even virtual clock stability is not asserted by these functional results.

## lifecycle: M2 lifecycle and filter-semantics claim record

**Scope:** [§FS-lifecycle.model](FS-lifecycle.md#model-executable-controller-and-effect-contracts), [§FS-lifecycle.filter](FS-lifecycle.md#filter-general-action-of-the-preserved-m1-program), [§FS-lifecycle.resources](FS-lifecycle.md#resources-identity-ownership-and-bootstrap),
[§FS-lifecycle.supervision](FS-lifecycle.md#supervision-stable-ownership-and-typed-results) and [§FS-lifecycle.cancellation](FS-lifecycle.md#cancellation-requests-races-and-teardown). For every reachable
finite modeled lifecycle, entry requires the exact eight-operation plan and all
modeled bootstrap, namespace, handle, credential, decoder, NNP and filter receipts.
Invalid bytes cannot enter. Every live descendant retains its scope, every UID/GID form set to 65534, empty supplementary groups, all five
capability sets zero, NNP and filter. Setup failure has no successful setup continuation. Release may
target only owned handles after namespace death. Cancellation requests retain the
live scope and may race with exec; lost reports preserve history while changing
knowledge to unknown. The successful segment refines the unchanged M1 event trace.

For every pair of UInt32 architecture/syscall words, a separate bytecode machine
running the canonical nine instructions returns kill for another architecture or
an unsigned syscall word at least 0x40000000, EPERM for lower native getppid, and
allow for other lower native words. Executing unsupported instructions/loads/targets or
exhausting fuel cannot produce an allow result. The decoded-tag corollary links the
original decoder to this semantics; it does not prove Linux's interpreter/JIT.

Full types and exact per-theorem transitive axioms for **31 named authored claims**
and **274 total M2 theorem declarations** are reviewed in `assurance/m2-claims.json`.
The names below are in `LeanCageM2`, except the explicitly named bytecode namespace.

| Declarations | Reviewed proposition |
|---|---|
| `initial_safe`, `establish_safe`, `step_safe`, `reachable_safe` | Empty initial state; receipt effects preserve safety; every reachable state has the conditional launch and descendant invariant |
| `descendant_secure`, `failed_no_setup`, `release_owned_only` | Inheritance including full normalized credentials for every live member; no successful setup after failure; cleanup releases only a member of the owned handle set |
| `request_preserves_members`, `death_empties_scope`, `lost_report_unknown` | Request differs from observed completion; namespace death empties scope; reporting loss does not erase actual historical entry |
| `success_was_requested`, `preparePlan_iff` | Responses correspond to the pending controller operation; Main's actual preparation succeeds exactly for M1 ValidInput and the fixed plan |
| `initial_ordered`, `establish_ordered`, `step_ordered`, `reachable_ordered`, `entry_requires_plan` | Exact prefixes and complete required order for every reachable entered state |
| `step_decoded`, `reachable_decoded`, `invalid_input_never_enters` | Decoder receipts are tied to actual decoding for arbitrary ABI/snapshot; invalid input never enters |
| `plan_refines_m1`, `projected_m1_replay`, `reachable_m1_refinement`, `replay_extends_reaches` | All reachable entered lifecycles compose with M1; executable finite replay preserves inductive reachability |
| `success_witness`, `cancellation_exec_race`, `request_can_precede_exec`, `descendant_teardown_witness` | Concrete accepted input and useful success/fork/re-exec/escape/cancel/death executions; no universal syscall-success premise |
| `Bytecode.canonical_action`, `Bytecode.decoded_action`, `Bytecode.zero_fuel` | General unsigned action, decoder-tag linkage and fail-closed fuel boundary |

**Proof premises and foundations:** reachability is generated from the empty initial
state by the executable transition function, including errors, interruption,
contract violations, reporting loss and hostile fork/exec/exit/escape/signal events.
Backend success/death observations are truthful OS-effect contracts when this
model is applied to Linux; no new Lean axiom asserts them. The per-claim axiom union
is only `propext`, `Classical.choice`, `Quot.sound`. The gate rejects custom,
unfinished and compiler-trust axioms. These are partial-correctness results;
scheduling, SIGKILL delivery and terminating kernel operations remain additional
liveness premises. Outside victim state, workspace/network/IPC authority and
hardware observations are not proved by this model.

**Implementation and test evidence:** a separate dependent Lake package under
`m2/` preserves root dependencies. Main validates actual bounded input before
emitting a fixed plan to a fresh static helper. The native source/effect and M1
premise maps, selected ABI, concrete syscall/ownership/error interfaces and eight
open M4 obligations are recorded in the lifecycle architecture and handoff review.
`assurance/m2-vm-evidence.json` records **43 passing cases** plus capable-kernel
positive controls, a fresh pinned Linux source/configuration build, all guest
image entries, actual binaries/runtime/compiler/kernel/QEMU/firmware identities,
exact VM command/environment and raw `assurance/m2-vm-transcript.log` identity.
Guest exit 125, repeated exec, double-fork/setsid, failed reporting, interrupted
setup, actual cancellation/death, inherited aliases and preservation of an
unrelated sentinel are checked explicitly. Injected error/death/report/rename
fixtures are labeled; neither their counts nor theorem counts measure security.

**Identities and validation:** the M2 manifest binds source, contracts, dependency
locks, audit/tests and VM evidence by SHA-256. `python3 scripts/audit_m2.py` builds,
checks every theorem/module and preserves all **445 original M1 theorem types and
axiom sets** against the byte-for-byte copied original manifest
`assurance/m1-reviewed-baseline.json`. It writes checked `.olean` identities to
`.tools/assurance/m2-report.json`. The original 43 M1 named claims, 18-claim decoder
baseline, M1 native driver, kernel profile and raw VM evidence remain unchanged.
These are local source/artifact records, not a published release.

Run `./scripts/check.sh` for the full handoff gate, including 33 additional Lean
guards and M2 audit/evidence rejection tests. `python3 scripts/run_m2_vm.py --prepare`
builds and replays the separate VM; `--check-evidence` checks historical structure
and source identities; `--check-artifacts` additionally compares recorded current
artifacts. The normal gate compiles native code without running guest workloads
on the development host. The handoff verdict is in `docs/reviews/M2-handoff.md`.

**Residual trust and absence of stronger claims:** A-logic, A-model, A-entry,
A-linux, A-executable, A-platform, A-hardware, A-observer and liveness aspects of
A-resources remain applicable. Sealed objects and normalized inheritance replace
specific M1 entry premises, while root administration and trusted images remain
explicit. Native C/Lean/libc/process/loader/ABI refinement, Linux enforcement and
hardware fidelity remain open M4/M5 obligations. The public fixture root and broad
filter are not an M3 workspace policy, functional confidentiality proof or
production sandbox. The destination [§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) remains unchanged.

## workspace: M3 workspace model and VM evidence

**State: M3.1–M3.7 accepted for the conditional model and tested VM profile;
full handoff gate passed on 2026-10-31.** [§FS-workspace](FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) fixes the supported offline
shell/Python runtime, object authority, interference, disclosure, resource and
private-report contracts. It is a VM-only conditional profile; no production
sandbox or end-to-end executable correctness is asserted.

**Propositions:** `assurance/m3-claims.json` records full types, hypotheses and
transitive axioms for all 419 M3 theorem declarations across 12 modules, with
60 named authored claims. The
plain-language mapping is `docs/reviews/M3-handoff.md`:

| Declarations in `LeanCageM3` | Security scope and premises |
|---|---|
| `reachable_issued_handles`, `reachable_unguarded_read`, `issued_write_preserves_protected` | Starting with closed inherited handles and arbitrary object/name maps, every finite request trace preserves live authorized handles. Held-handle reads/writes need no new ownership check; guest name tricks do not grant outside/sibling authority. |
| `guest_preserves_protected`, `guest_trace_preserves_protected`, `runtime_trace_preserved` | Every guest step/guest-only trace preserves existing nonwritable objects; runtime bytes also persist under permitted ordinary external writes. Host/sibling writes to their own objects remain explicit. |
| `descendant_inherits`, `reachable_processes_safe` | Admission establishes full run credentials/root/namespace/grants/NNP/filter/scope; arbitrary modeled fork/exec/exit traces retain them. |
| `validatePolicy_iff`, `decodePolicy_iff`, `decodePolicy_bounds`, `accepted_policy_filter_action` | Exact typed bound checks, byte-decoder decomposition into structural recognition plus checks, and actual accepted-policy linkage to universal filter semantics. No separate external JSON grammar or native parser refinement theorem. |
| `Filter.program_action`, `Filter.policy_filter_action` | Every UInt32 architecture/syscall/argument-word input produces the specified allow/EPERM/ENOSYS/kill action for the generated instruction list. No sampled-input premise. |
| `entry_requires_receipts`, `reachable_entry_ordered`, `lifecycle_projection` | Entry needs the complete ordered setup receipts; successful histories erase to M2's operation plan without borrowing its fixed-UID/image/filter invariant. |
| `private_report_knowledge`, `decodeResult_valid`, `cancel_not_completion`, `release_requires_extinction` | Guest byte streams cannot establish trusted knowledge; decoded results satisfy the explicit checks; cancellation/report loss cannot invent completion or cleanup. Native transport ownership remains an effect contract. |
| `resource_scope`, sampling/OOM/capture/task/lease/reservation lemmas | Members retain the run scope; delivered monotone samples trigger requests; OOM evidence needs an increase; explicit task/capture/admission bounds and no reuse before extinction/release. Linux accounting and scheduling remain assumptions. |
| `reachable_model_safety`, useful execution witnesses | Composition of those local model properties over arbitrary component traces, with inhabited read/write, entry and descendant executions; not a native concurrent simulation. |

**Foundations and limits:** the transitive logical axiom union is only `propext`,
`Classical.choice`, `Quot.sound`. The auditor rejects custom, unfinished and
compiler-trust axioms and compares the complete declaration inventory. Models
use UInt32/UInt64 identities/words plus bounded values; concrete ABI conversions,
VFS/mount/mmap effects, loader/runtime, private pipe authenticity and Linux resource
behavior remain explicit correspondence obligations. These are partial-correctness
results, not termination, functional noninterference or hardware-channel proofs.

**Native and test evidence:** 60 fresh VM workload cases, three API checks and
six death/cancellation boundaries pass. The separate `m3/` package and original static helper
implement copied input/stdin, frozen runtime, private workspace, per-run IDs,
namespace/capability/handle restriction, generated cBPF, cgroups, private framed
results, bounded output and post-extinction export. Actual `check`, `run` and
`report` use the same helper. The [acceptance matrix](../reviews/M3-acceptance.md)
maps useful workloads, denial/failure/race cases and finite coverage limits.
`assurance/m3-vm-evidence.json`, `m3-vm-transcript.log` and
`m3-image-inventory.json` hold source-bound outcomes, exact executable/kernel/image/
emulator/firmware/library hashes, versions, command, explicit environment overrides
(with other host variables inherited) and the complete image inventory. The theorem audit adds checked `.olean` identities in
`.tools/assurance/m3-audit.json`. These are local evidence artifacts, not a release.

**Runtime/provenance:** `profiles/m3/runtime-lock.json` binds four OCI layers/diff
IDs, Python 3.13.18, Dash 0.5.12-2, glibc 2.36, exact entrypoint/loader bytes and
97 package notices. Passive ELF inspection covers 792 objects; only unsupported
Tk lacks dependencies. Upstream artifact/build identity is not a reproduced build
attestation. Linux 6.18.59 has a separate reviewed M3 configuration. The functional
VM uses QEMU TCG, one `max` vCPU, 2048 MiB and ACPI-PM, with no external NIC, disk,
KVM or host mount. Physical CPU/microcode verification is absent because M3 makes
no physical-hardware claim.

**Validation:** the full `./scripts/check.sh` gate includes 74 Python tests, 168 Lean
guards, all three theorem audits, native compilation and archived evidence.
M3 adds 32 Python tests and 77 guards, with 84 reviewed source/evidence identities.
The [main review](../reviews/M3-main-review.md) records rerun results after the
report-storage correction. Failed report publication retains known execution,
cleanup and cancellation observations under [§FS-workspace.results](FS-workspace.md#results-entry-cancellation-and-bounded-transport);
three disposable filesystem tests cover successful publication and both write
and rename failures. These tests execute no guest workload on the host.
Run `./scripts/check.sh` for full proof, specification, pure fixture,
compile-only and archived evidence checks. Explicit `python3 scripts/run_m3_vm.py`
replays the VM; `--check-artifacts` additionally compares current artifacts.
The archive checker works from a moved checkout and rejects stale/mixed identities
or incomplete/tampered observations. Preserve all 445 M1 and 274 M2 declarations,
dependency/toolchain pins, native sources and raw evidence; only reviewed shared
source fingerprints change in their current manifests.

**Residual assumptions:** A-logic, A-policy, A-model, A-entry, A-linux, A-executable,
A-platform, A-hardware, A-observer and the named liveness/accounting aspects of
A-resources. Root-owned immutable artifacts and reserved UID/cgroup allocation
remain trusted. Unknown cleanup quarantines identities and active reservations;
retained results require operator capacity. All native/parser/loader/VFS/FFI/
compiler/Linux/crypto and artifact connections stay open under M4. The selected
Clight experiment and partial source connections are recorded under [§FS-assurance.native](FS-assurance.md#native-partial-m4-reporting-source-evidence);
neither source mapping nor VM testing substitutes for correspondence. All timing/cache/contention/speculation observations in
[§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) remain M5. No secrecy guarantee follows from output
being explicitly authorized.

## native: Partial M4 reporting-source evidence

**Scope:** [§FS-workspace.results](FS-workspace.md#results-entry-cancellation-and-bounded-transport), limited to local source execution in the pinned
Clight model plus explicit byte-aware effects and asynchronous loss. The maintained
260-line extraction and generated AST remain unchanged. `assurance/m4-claims.json`
retains the 25 feasibility declarations and 12 Lean target records;
`assurance/m4-connection-claims.json` inventories every additive Rocq declaration
with its complete type and transitive assumptions and the unchanged 12 Lean
endpoint claims. The public endpoint checkpoint preserves all 1113 Rocq records and 212 compiled
Rocq module identities. It contains 103 Lean theorem records: twelve preceding
records and 91 additions, comprising 67 authored proofs and 24 generated equation
or proof helpers. These counts identify the audited inventory, not a security
score.

**Results:** universal finite-prefix safety and exact returns for `write_all`,
`error_number`, `get32`, `get64`, `put32`, `put64`, `fault`, `result_of`, `decode_frame`, `send_frame` and `finish`; source codec round
trips for all 32/64-bit words; defined ordinary progress rather than loss/wait
witnesses. The extended machine retains old transitions and earlier universal
source safety. Explicit comparison/copy/close/exit contracts have owned-memory
progress, exact comparison equality, non-prefix partial-copy loss, unchanged
outside memory and terminal nonreturning exit properties. `fault` compares actual
owned strings through the maintained global pointer and supports arbitrary signed
comparison magnitudes. Constructed source runs allow arbitrary caller
continuations and finite waits. Universal local return claims end at `Kstop`. The complete result constructor
executes 161 source steps, including all 50 initialization stores, the whole
144-byte structure copy and actual local free. Completed fields match arbitrary
input/global words; other fields/digest bytes are zero. Every finite prefix
preserves caller memory outside the output, and loss retains current memory.
The structure copy includes padding memory values, without claiming initialized
padding or compiled-copy atomicity. Actual helper execution now composes with
caller continuations in both directions, preserving all memory effects and events.
The complete child-failure routine allocates and fills its eight-byte local in
96 source steps before fault selection. Every finite live prefix has an ordinary
enabled step; local execution never returns to its caller. Every trace sends a
prefix of the source-selected zero-, three- or eight-byte report, including a
transfer interrupted by loss. Every exit attempt uses code 125. Independent
owned inputs and complete normal, dropped, short, failed and lost executions
are constructed for arbitrary descriptor/stage/error words. This is partial
correctness and progress availability, not termination, successful publication,
whole-program initialization or Linux exit/resource-reclamation correspondence.

The complete private-frame decoder derives every read from arbitrary owned
160-byte input, actual globals and an independent writable 144-byte output.
Its complete source predicates determine the return: header failures preserve
all old caller memory; later failures retain the constructed output. All seven
accepted tags, rejected tag/default branches, short-circuit checks and both
reserved-byte loops execute actual source. Every finite live prefix has ordinary
progress or an exact return. Outside-output memory is preserved through loss,
and every return frees the actual local structure. Allocated inputs inhabit all
seven accepted tags and early/late rejection. Finite successful runs coexist
with arbitrary comparison waits and loss; no termination claim follows.

The complete sender starts from independent readable 144-byte result ownership,
arbitrary 32/64-bit fields and all 32 digest bytes. It derives the by-value copy,
160 zero stores, both library copies, every byte writer and all five ordered
fault checks. Every returned trace is exactly the selected report on zero or a
proper prefix on -1. A zero return can report zero, seventeen, 160 or 320 bytes;
it does not by itself establish one complete frame. Every finite trace is a
prefix of the selected bytes, and old memory outside the TLS error cell is
preserved even after loss. Both local allocations are actually freed on return.
Stable selector strings survive duplicate-report I/O. `finish` executes the
complete sender and then returns the source exit mapping regardless of
publication failure, freeing its own copy. EXITED/SIGNALLED detail bounds are
explicit when claiming the intended small exit-status domain.

Allocated inputs and complete successful source runs inhabit normal, drop,
short, duplicate, wrapped wrong-sequence and bad-reserved-byte reports. Failed
writes emit no bytes and return -1; a one-byte transfer can be followed by loss
after any finite number of waits. Whole `finish` executions inhabit both full
publication and ignored publication failure. The restricted certificate used to
construct successful witnesses is not used by universal source guarantees.

The complete terminal-error receiver starts from caller output ownership, stable
run/UID globals, a writable TLS cell and arbitrary wrapper control words. It
derives all seven local allocations, the descriptor store and each bounded read.
Every finite execution reads at most nine bytes, including partial-transfer loss.
Every completed return classifies its own read trace, executes the selected result
constructor, both typed copies and all seven frees. A SETUP output implies exactly
eight bytes, initial bad and entered flags zero, stage 1..8 and error 1..4095.
Close errors are ignored exactly as in the source; they provide no cleanup receipt.
Every finite prefix preserves old memory outside output and TLS and has ordinary
progress or an exact return. Allocated complete runs include arbitrary finite EINTR
prefixes, short/malformed/ninth-byte input, fatal errors after a prefix, close
errors, exits and signals. A complete raw-status-65 run returns signal detail 65:
valid Linux wait-status and intended signal-domain provenance remain obligations.

Actual outgoing frames recover every field and digest, with the kind narrowed
to its low byte. The private decoder's exact acceptance is stated over those
fields; its late rejection still writes narrowed fields and a cleared reserved
tail. Run/sequence mismatch preserves old caller memory. Actual successful sender
histories with fault selection disabled connect to actual decoder histories whose
owned input contains the emitted bytes. Allocated complete pairs include accepted
private controls, raw kind 256 narrowing to zero, rejected signal detail 65,
CANCELLED and nonzero reserved fields. The private and final-public languages
remain distinct.

Under explicit equality between an actual child reporting trace and receiver
read trace, an actually stored SETUP result contains the child's original stage
and error words, with the specified bounds. Shorter child reports cannot supply
that eight-byte result. An allocated complete child/receiver pair retains child
exit request 125, arbitrary finite EINTR retries and close waits, and ignored close
failure. These are source observation connections with separate ownership
premises; Linux transport provenance and whole-program ordering remain open.

The live public Lean decoder now has an exact acceptance characterization over
its header, entry, cleanup, all field offsets and the live validity predicate.
Every accepted field fits its actual byte width. A separate proof-side public
encoder has a complete round trip for width-correct records with 32 digest bytes:
the live decoder returns exactly the live validator on the original record.
Six useful public results are accepted and private controls, a two-byte kind 256
and signal detail 65 are rejected in concrete ordinary-kernel witnesses. This
public encoding of kind 256 is distinct from the private sender's low-byte
narrowing. The proof-side encoder does not alter deployed behavior or establish
cross-assistant, transport or observation provenance.

The separate strict bridge experiment proves an exact decoder normalization and
imports its complete computational closure into an isolated Rocq 9.3 profile.
Explicit byte and arithmetic adapters connect the imported 32-bit and 64-bit
reader values to actual C executions, with unchanged memory, exact 59/103-step
successful traces, progress, every-prefix loss and allocated nonvacuity. It adds
42 Rocq and 33 Lean theorem records while preserving the earlier 1113/103 records
and established proof profile. The imported logical model uses SProp and five
declared instances of definitional UIP; the new Lean proofs use quotient
soundness and propositional extensionality. The subsequent [complete imported-frame
connection](../reviews/M4-frames.md) preserves those records and proves total slice
and equality operations, all source-frame fields, exact parsing/rejection order,
and the full validity predicate. Actual sender observations yield the complete
imported decoder result, with allocated arbitrary-field executions and eighteen
accepted/rejected source witnesses. Source kind narrowing remains explicit.
Translation-faithfulness review, whole-controller composition and Linux/executable
correspondence remain open; this is not a completed cross-assistant guarantee.

The [native decimal parser connection](../reviews/M4-controller-number.md) adds
83 Rocq records for [§FS-workspace.policy](FS-workspace.md#policy-bounded-typed-request). It connects the unchanged
`number` source to the exact nonempty decimal language and unsigned 64-bit bound,
including short-circuit overflow checks, signed/unsigned byte reads, leading
zeros and output/input aliasing. Constructed complete source paths support
all-return correctness, finite-prefix memory/permission preservation, ordinary
progress and loss at every source boundary. Twenty accepted/rejected cases each
have allocated overlapping and separate source executions. The machine remains
sequential; absence of interfering writers, deployed store atomicity, argument
provenance, policy bounds and whole-controller ordering remain obligations.

The [live plan connection](../reviews/M4-plan.md) adds exact argument layout and
decimal UTF-8 facts for the actual Lean encoder. Its ten serialized limits fit
the unsigned range when the live policy predicate succeeds; parent identity and
the actual runtime argument table remain obligations. A strictly imported numeric
byte interface has the same complete acceptance/rejection language and value as
the native parser, and its results determine actual owned source runs, stores,
prefixes and loss. The separate and overlapping allocated witnesses retain all
twenty earlier cases. This adds 32 Rocq and 88 Lean theorem records, with the
imported logical model and translation-faithfulness boundary stated explicitly.

The [complete-helper numeric block](../reviews/M4-main-input.md) adds 107 source
and memory declarations for the ten field-pointer initializers and actual parser
loop. It replays all 83 parser records against the complete helper and checks
exact function identity. Successful fields are stored in order; a later rejection
retains those stores and stops before its reporting call. Owned arguments remain
stable across the writes. Constructed paths retain every interruption boundary
and preserve memory outside the two 80-byte write regions. Sixteen allocated
source witnesses begin with constructible full-program initial memory; they do
not establish reachability through earlier main-routine checks. The imported
numeric byte interface determines the same stored vector and stopping decision.
Actual argument provenance, parent checks and the remaining controller still
need their own connections.

The [policy-bound connection](../reviews/M4-policy-bounds.md) adds 64 Rocq and 36
Lean records for the actual argument-count/byte condition, nineteen numeric
guards and final rejection branch. Exact source paths preserve short-circuit
order, leave memory unchanged and reach the selected endpoint within 140 steps;
every boundary permits loss. Successful numeric stores establish their readable
policy image. The strictly imported computational predicate determines the same
endpoint, and ordinary Lean proofs relate it to the live policy limits and
argument totals. The fixed CPU period remains separate from serialized limits.
Twenty-six allocated source witnesses cover accepted boundaries, each rejected
guard and machine extremes. These local statements do not establish the earlier
argument accumulation, parent/digest/export/allowlist checks or whole-main entry.

The [argument-loop connection](../reviews/M4-arguments.md) adds 114 Rocq and 23
Lean records for the actual initialization, signed loop, `strlen` boundary,
per-string rejection and unsigned accumulation. Independent argument-table and
terminated-string ownership produce accepted and first-rejected paths. Each
accepted string is bounded before addition, so the total cannot wrap even at
the maximum signed argument count. The complete selected block takes at most
26 times the guest argument count plus 13 non-wait steps; composition with the
actual policy block adds at most 141. Every bounded actual prefix preserves
memory, with defined live progress, exact endpoints and loss at every boundary.
Library waiting remains arbitrary. Twelve allocated cases cover nine accepted
and three rejected length scans; the composed policy block accepts seven and
rejects five. A further witness repeats the same string pointer in two table
cells. The strict imported length predicate agrees with source acceptance and
the successful total. Rejection retains the preceding valid prefix's total,
not the reference sum over all arguments. Physical argv and libc correspondence,
earlier parent/digest/export/allowlist checks and whole-main entry remain open.

The [digest recognizer connection](../reviews/M4-digest.md) adds 86 Rocq and 193
Lean full records, including generated Lean equations and helpers. Owned strings
construct complete actual function paths and exact zero/one returns for
sixty-four lowercase hexadecimal bytes. The signed-byte reads, repeated loads,
unsigned loop and first rejection are checked. Every isolated execution preserves
memory and has defined live progress or the exact return, with arbitrary library
waiting and loss. The finite bound is 2,068 non-wait steps, or 2,069 events when
including loss after return; no prefix-bound premise or termination claim is
used. Eighteen allocated cases and two NUL-boundary cases establish useful and
rejected executions. The strict imported byte predicate agrees with the source.
The actual live `digestField` success implies a valid stripped UTF-8 suffix,
which the existing plan places at native positions fourteen and fifteen.
The enclosing JSON parser, physical argv, the native caller's `none` and digest
checks, authentication of content and whole-controller behavior remain separate.

**Evidence and assumptions:** `assurance/m4-public-evidence.json`,
`assurance/m4-wire-evidence.json`,
`assurance/m4-receiver-evidence.json`,
`assurance/m4-sender-evidence.json`,
`assurance/m4-decoder-evidence.json`,
`assurance/m4-library-evidence.json`,
`assurance/m4-structures-evidence.json`, `assurance/m4-callers-evidence.json` and
[the caller proposition review](../reviews/M4-callers.md) and [decoder proposition review](../reviews/M4-decoder.md) and
[sender/finish proposition review](../reviews/M4-sender.md) and
[receiver proposition review](../reviews/M4-receiver.md) and
[report-byte proposition review](../reviews/M4-wire.md) and
[public endpoint review](../reviews/M4-public.md) bind sources, terms, preservation
checks and raw command receipts. `./scripts/check_m4_connection.sh` replays the
pinned tools, actual extracted source/AST, complete declarations and `coqchk`.
The isolated profile has its own [bridge review](../reviews/M4-bridge.md),
`assurance/m4-bridge-claims.json`, `assurance/m4-bridge-evidence.json` and
`python3 m4/bridge/check.py` replay. Its additional logical model is kept explicit.
The controller parser has its own `assurance/m4-controller-number-claims.json`,
`assurance/m4-controller-number-evidence.json` and `python3 m4/controller/check.py`
replay, preserving the complete frame checkpoint byte-for-byte. Its 83 records
use no new foundation: 49 report none, 29 the existing six and five the existing
four logical foundations. That parser package adds no Lean result. The subsequent
plan connection has `assurance/m4-plan-claims.json`, `assurance/m4-plan-evidence.json`
and `python3 m4/plan/check.py`; it preserves all preceding native/parser/frame
records and artifacts. Its imported endpoint uses four explicit definitional-UIP
instances. The [plan review](../reviews/M4-plan.md) records the exact transitive
foundations in both proof assistants. The numeric-block gate is
`python3 m4/main/check.py`, with `assurance/m4-main-input-claims.json` and
`assurance/m4-main-input-evidence.json`. It records the complete helper's actual
header inputs, all new/adapted propositions, exact function identity, a rejected
compiled mutation and independent kernel replay. Earlier manifests and receipts
are preserved, with explicit documentation-fingerprint amendments. The bounds
gate is `python3 m4/policy/check.py`, with
`assurance/m4-policy-bounds-claims.json` and
`assurance/m4-policy-bounds-evidence.json`. It preserves the numeric-block
checkpoint and records the exact imported predicate, rejected descriptor
mutation, failed direct-import experiments and full foundation inventory.
`python3 m4/arguments/check.py`, `assurance/m4-arguments-claims.json` and
`assurance/m4-arguments-evidence.json` add the argument loop, its conservative
`strlen` effect, exact imported profile and the preserved bounds checkpoint.
The gate checks all 151 export entries, nineteen compiled identities, twelve
integrity regressions, a rejected source-limit mutation, disabled-check rejection
and independent kernel replay.
The digest gate is `python3 m4/digest/check.py`, with
`assurance/m4-digest-claims.json` and `assurance/m4-digest-evidence.json`. It checks
the 149-entry axiom-free computational export, sixteen compiled identities,
complete foundations, twelve integrity regressions and compiled negative
controls, preserving the argument checkpoint. Generated Lean helper propositions
are printed with their proof arguments; no compiler-trust axiom supports the
closed examples. Full M4 remains open.
The established Coq 8.18 profile's six foundation/semantic-parameter entries remain unchanged; the explicit
machine excludes stock external/builtin execution. No new Lean axiom is added.
The owned witnesses allocate cells for the actual source symbol mapping; they do
not assert reachability from whole-program entry. Native/compiler/kernel/runtime
and hardware identities remain the preserved earlier profiles, not new execution
evidence. No native guest workload is run on the shared host.

The caller checkpoint's local replay depended on fifteen historical module
names with source only in the ignored build directory. The decoder checkpoint
maintains and audits those exact dependencies, preserving previous statements
and artifacts, and rejects undeclared imports. The earlier receipt did not by
itself establish replay from only maintained proof inputs.

**Open:** cross-routine and surrounding controller/storage composition, valid
Linux wait-status provenance, checked C/Rocq-to-Lean translation,
all sixteen original M2/M3 Linux/native ledger entries, libc/Linux interference,
compiler/runtime/linker/loader correspondence and independent composed-profile
review. M4 remains incomplete. Hardware channels remain [§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels).

## assumptions: Initial assumption and obligation register

These are prospective boundaries, not assertions that the current repository
already meets a security claim. Every later theorem must list the subset it uses.

| Key | Boundary | Early treatment | Planned disposition |
|---|---|---|---|
| A-logic | Lean logic, kernel/checker and faithful checking execution | Foundational trust, pinned checker | Audit axioms and proof-checking provenance; remain explicit |
| A-policy | Operator-selected policy, declared public/secret inputs and disclosures | Explicit environmental premise | Validate syntax/feasibility; cannot prove operator intent |
| A-model | Abstract effects represent all relevant concrete behavior | Open obligation | M1–M4 refinement, failure and interference coverage |
| A-entry | Trusted dedicated child, private stable filter/executable/argv/environment, no hostile writers/tracers/handlers or existing filters | Explicit M1 entry profile, checked/tested native setup where applicable | M2 extend to adversarial inheritance/aliases/races; M4 native correspondence |
| A-linux | Relevant Linux enforcement, syscall semantics and transitive dependencies | Assumed in early Linux demonstrations | M4 connect contracts to pinned Linux implementation; expose remaining scope |
| A-executable | Lean compiler, native runtime, FFI, bindings and loader preserve semantics | Assumed for early binaries | M4 artifact correspondence; no perpetual hidden runtime gap |
| A-platform | Boot, configuration, privilege setup, deployment and updates match the profile | Explicit deployment assumptions | Bind artifact identities and configuration; verify relevant software setup |
| A-hardware | CPU/memory/device behavior matches the formal hardware model | Foundational fidelity assumption | M5 specify software-visible behavior; retain physical model fidelity openly |
| A-observer | Observation model covers the stated attacker | Open modeling obligation | Logical traces first, hardware-aware traces in M5; no silent exclusions |
| A-resources | Accounting/scheduling/termination implement each advertised bound | Assumed until established | Discharge per supported limit; otherwise narrow the claim |

## closure: Rules for stronger claims

Use states such as planned, model-proved, tested, and profile-verified with a stated
scope; multiple kinds of evidence can coexist. A model proof may still depend on
unproved assumptions. Reserve an end-to-end claim for a named profile whose
advertised chain is established, leaving only explicitly accepted foundational
assumptions. Do not reclassify unfinished Linux or compiler work as foundational
trust merely to close a milestone.

## updates: Evidence expires with its dependencies

Changes to specifications, theorem statements, code, toolchains, platform settings,
or artifacts must trigger review and revalidation of affected claims. An update
must not inherit an old certification merely because its version name is similar.
