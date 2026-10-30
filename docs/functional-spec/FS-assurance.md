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
| Validated authority | [§FS-policy](FS-policy.md#fs-policy-grant-only-explicit-supported-authority) | Planned | Specification | Implementation and theorem |
| Canonical filter decoding | [§FS-filter-loading.input.correctness](FS-filter-loading.md#inputcorrectness-decoder-proof-boundary) | Model-proved; pure executable checks | [§FS-assurance.decoder](FS-assurance.md#decoder-m12-decoder-claim-record); exact acceptance, bounds, rejection and nonvacuity proofs; axiom gate | Native executable and FFI field-copy correspondence |
| M1 fail-closed launch order | [§FS-filter-loading.installation.model](FS-filter-loading.md#installationmodel-executable-launch-semantics-and-proof-obligations) | Model-proved; VM-tested native slice | [§FS-assurance.launch](FS-assurance.md#launch-m13-launch-order-claim-record) and [§FS-assurance.demo](FS-assurance.md#demo-m14-isolated-linux-test-record); actual-decoder linkage, exact successful order, terminal failures, native call map and 13 VM cases | Native/source/compiler/runtime/FFI and Linux correspondence; broader M2 lifecycle |
| M2 owned lifecycle and filter action | [§FS-lifecycle.model](FS-lifecycle.md#model-executable-controller-and-effect-contracts) and [§FS-lifecycle.filter](FS-lifecycle.md#filter-general-action-of-the-preserved-m1-program) | Model-proved; VM-tested; handoff gate passed | [§FS-assurance.lifecycle](FS-assurance.md#lifecycle-m2-lifecycle-and-filter-semantics-claim-record); exact plan, ownership/inheritance and general bytecode action; source-bound VM evidence | Native/Linux correspondence; M3 authority; M5 hardware channels |
| Native workload confinement | [§FS-isolation](FS-isolation.md#fs-isolation-confine-all-supported-guest-effects) | Planned | Specification | Launcher, filesystem/process model, enforcement proof |
| Bounded resources | [§FS-resources](FS-resources.md#fs-resources-define-and-enforce-supported-resource-limits) | Planned | Specification | Precise supported limits and enforcement |
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
