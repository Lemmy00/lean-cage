# AR-filter-slice: M1.1 source map and typed contract boundary

This slice fixes the interfaces needed for [§FS-filter-loading.input.abi](../functional-spec/FS-filter-loading.md#inputabi-m1-native-x86-64-profile),
[§FS-filter-loading.input.subset](../functional-spec/FS-filter-loading.md#inputsubset-one-canonical-restrictive-filter), and [§FS-filter-loading.installation.states](../functional-spec/FS-filter-loading.md#installationstates-launch-states-and-permitted-effects).
Its M1.1 output is source review and compiled contract declarations. M1.2 now
implements and proves the pure decoder in [§AR-filter-decoder](AR-filter-decoder.md#ar-filter-decoder-byte-decoder-proofs-and-executable-evidence-audit).
[§AR-m1-launch](AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration) adds launch transitions/proofs, a native binding, and the VM-only
demonstration. Full confinement and native/Linux correspondence remain open.
The profile and compatibility choices are recorded in [§DA-m1-filter-profile.choice](../decisions/architectural/DA-m1-filter-profile.md#choice-small-native-profile-and-explicit-departures).

## source: Pinned Bubblewrap path

The reference is Bubblewrap v0.13.1, commit
`362936aea0d5c6e70f7af75d2d44b5a914cb4ba2`. The following are source line numbers
at that commit, not observations of the host's installed binary.

| Reference location | Observed behavior | Contract consequence |
|---|---|---|
| [bubblewrap.c:2384–2426](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L2384-L2426) | Parses single `--seccomp` and repeatable `--add-seccomp-fd`; mixing fails; the latter immediately consumes its FD | M1 supports one snapshot, without these CLI options or list composition |
| [utils.c:627–674](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/utils.c#L627-L674) | Reads to EOF, retries `EINTR`, grows storage with an `SSIZE_MAX` guard, appends a non-payload NUL; errors return NULL | M1.2 decodes a finite snapshot; an eventual reader needs a cap and ownership/error contract |
| [bubblewrap.c:246–265](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L246-L265) | Reads and closes the owned FD; invalidates its slot; requires a multiple of eight; assigns `size_t len / 8` to `sock_fprog.len`; casts data to instructions | Validate before narrowing; decode bytes explicitly |
| [bubblewrap.c:269–285](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L269-L285) | Installs in linked-list order using `prctl`; `EINVAL` has a specific diagnostic; every install error exits | One required install with distinguishable terminal failure |
| [bubblewrap.c:2927–2929](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L2927-L2929) | Sets no-new-privileges early; failure exits | Require success before install; M1 places this after validation |
| [bubblewrap.c:3438–3443](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L3438-L3443) | Deferred single-FD loading follows privileged setup | M1 begins after unrelated preparation; that setup is not thereby verified |
| [bubblewrap.c:3479–3517](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L3479-L3517), [bubblewrap.c:614](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L614) | Optional fork creates an init branch, which also installs filters | M1 covers the exec child only; fork, init and supervision remain M2 |
| [bubblewrap.c:3519–3541](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L3519-L3541) | Closes selected FDs, unblocks SIGCHLD, sets parent-death behavior and ambient capabilities, then installs | Preparation effects and inherited handles/signals remain entry obligations |
| [bubblewrap.c:3541–3566](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L3541-L3566) | After install, optionally writes a notification, adjusts argv, calls `execvp`; exec failure may notify again, preserves errno, and exits | Do not describe the reference as immediately executing after install; M1 omits notification, PATH lookup, and fallback |
| [utils.c:84–99](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/utils.c#L84-L99) | Saves errno, logs, and exits with status 1 | Terminal failure does not imply infallible diagnostics/cleanup |

This is a source map, not a C semantics or equivalence proof. An oversized count
may narrow before kernel validation in the reference; LeanCage rejects it instead.

## abi: Linux definitions and source identities

The existing Linux 6.18.59 reference resolves to commit
`1253a6aa5d104312bf0992afacc15220ae35bdf9`; this records source identity without
changing the selected version. The later VM image/configuration identities are
recorded separately under [§FS-assurance.demo](../functional-spec/FS-assurance.md#demo-m14-isolated-linux-test-record).
The [filter structures](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/include/uapi/linux/filter.h#L24-L35),
[instruction constants and ceiling](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/include/uapi/linux/bpf_common.h),
[seccomp data/actions](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/include/uapi/linux/seccomp.h#L38-L77),
[audit architecture](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/include/uapi/linux/audit.h#L393-L448),
[ELF machine number](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/include/uapi/linux/elf-em.h#L31),
[x32 marker](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/arch/x86/include/uapi/asm/unistd.h#L13),
[syscall table](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/arch/x86/entry/syscalls/syscall_64.tbl),
[prctl constants](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/include/uapi/linux/prctl.h),
and [errno constants](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/include/uapi/asm-generic/errno-base.h#L5)
ground [§FS-filter-loading.input.layout](../functional-spec/FS-filter-loading.md#inputlayout-serialized-instructions-and-bounds) and [§FS-filter-loading.input.subset](../functional-spec/FS-filter-loading.md#inputsubset-one-canonical-restrictive-filter).
The [seccomp usage contract](https://github.com/gregkh/linux/blob/1253a6aa5d104312bf0992afacc15220ae35bdf9/Documentation/userspace-api/seccomp_filter.rst#L45-L82)
describes prerequisites, errors, and inheritance; it does not prove Linux correct.

These SHA-256 values identify the raw files reviewed. Re-fetch from the named
commit and use `sha256sum` to reproduce the check. `.tools/references/` is only
an ignored local reading cache.

| Repository / path | SHA-256 |
|---|---|
| Bubblewrap / `bubblewrap.c` | `de141c805cb88f8faff9af1b3bb49098191fc67833b51b51fea84510ea4426ce` |
| Bubblewrap / `utils.c` | `467867ed425a360c87e44af51a3673cc9ea3fee5f22c9df097ec7006c07d8b8d` |
| Bubblewrap / `COPYING` | `dc626520dcd53a22f727af3ee42c770e56c97a64fe3adb063799d8ab032fe551` |
| Linux / `include/uapi/linux/filter.h` | `8b07bc3c8bcaa4b43318c43e588e36258bdc6a80848efce51158a274b664be7b` |
| Linux / `include/uapi/linux/bpf_common.h` | `adc9e87d1a335379ffe3658547635904cae6ccb8b7d1e578d0c25b50aa44db04` |
| Linux / `include/uapi/linux/seccomp.h` | `38a129b0b1e0c5cbae3b01bb159810a5cc290d7823d4c386f71d70b16e93d8dd` |
| Linux / `include/uapi/linux/audit.h` | `9d906005bd35b90266e68a80c1677f375009c2f72fd796d6655cec62fd9818f0` |
| Linux / `include/uapi/linux/elf-em.h` | `e72cca577a97d1fccc7f4e5d37b39b401a527a97f02e589255c247b63cb227d2` |
| Linux / `arch/x86/include/uapi/asm/unistd.h` | `a5dbdb6f1396798ef9ec26ccc9e465ffc85680060ec19849f2f8c265f33908fe` |
| Linux / `arch/x86/entry/syscalls/syscall_64.tbl` | `ae37c49896f869681c077b14a4722b7ea3909c1906de31a2e273eacdd496102b` |
| Linux / `include/uapi/linux/prctl.h` | `7e85c8d3898ecc05ea4ad5bd634ec114606a6a2f35534057db401de18e280277` |
| Linux / `include/uapi/asm-generic/errno-base.h` | `2c148e92b8318deeb767fabd60822113e575ee664ff09a1873aed8f7a495793c` |
| Linux / `Documentation/userspace-api/seccomp_filter.rst` | `cd51ec8cf62f5029614e8c14d43d52ce1b69efbdb73e1f8c7d1c93d646b06ad7` |

## contracts: Lean declarations and downstream ownership

`LeanCage/Linux/FilterContract.lean` contains fixed-width instruction fields,
the ABI descriptor, the single program tag/reference instructions, rejection
types, and the decoder function type for [§FS-filter-loading.input.errors](../functional-spec/FS-filter-loading.md#inputerrors-deterministic-rejection-and-decoder-interface).
It remains the contract type module. [§AR-filter-decoder.decoding](AR-filter-decoder.md#decoding-checked-reads-and-exact-reconstruction) adds the actual
decoder; [§AR-m1-launch.binding](AR-m1-launch.md#binding-small-native-boundary) separately implements native field copying and
OS calls without casting the byte snapshot into native structures.

`LeanCage/Launch/Contract.lean` contains portable stages, effect names, failures,
and observation traces for [§FS-filter-loading.installation.states](../functional-spec/FS-filter-loading.md#installationstates-launch-states-and-permitted-effects) and
[§FS-filter-loading.installation.failure](../functional-spec/FS-filter-loading.md#installationfailure-terminal-failures-without-rollback-claims). It imports no Linux module. These are
raw vocabulary, not a transition relation: an arbitrary event list is not a
permitted execution. [§AR-m1-launch.model](AR-m1-launch.md#model-total-transitions-and-trace-evidence) defines that relation over all documented
outcomes and proves install-before-exec with useful nonvacuity witnesses.
Detailed decoder errors remain in the decoder result; the portable
`validationRejected` observation classifies failure without replacing diagnostics.

`tests/integration/FilterContract.lean` independently interprets the four used
instruction codes for representative architecture/syscall words. It checks the
reference fixture without OS calls; it is neither the decoder nor a proof of
Linux enforcement. `./scripts/check.sh` builds the library then runs this check
as well as the existing documentation checks.

M1.2 supplies decoding and bounds proofs; M1.3 owns launch semantics and proofs.
Their shared vocabulary is fixed here; consequential changes update the contract
first. No CLI, policy language, or broad backend framework is introduced.

## bindings: Required OS and FFI contract

Under [§AR-linux.bindings](AR-linux.md#bindings-explicit-os-contracts), the binding must meet these contracts. M1's concrete
call map and native layout checks are in [§AR-m1-launch.binding](AR-m1-launch.md#binding-small-native-boundary); formal
native/compiler/runtime/Linux correspondence remains an assumption:

- On the selected LP64 ABI, native `sock_filter` has size 8, alignment 4, and
  offsets 0, 2, 3, 4. `sock_fprog` has a 16-bit count at offset 0, pointer at
  offset 8, size 16 and alignment 8. Verify with target C layout checks; Lean
  structures are not these native memory layouts.
- Copy fields into aligned private native storage. Keep it and the fprog live
  and immutable through installation; Linux copies the program on successful
  attachment. Release owned storage without freeing caller-owned memory or
  creating an alternate exec path on cleanup error.
- Use `prctl` operations 38 and 22, mode 2, with the exact arguments in
  [§FS-filter-loading.installation.effects](../functional-spec/FS-filter-loading.md#installationeffects-os-effects-and-post-install-boundary). Respect the variadic ABI, 64-bit
  argument/pointer passing, 32-bit return, and thread-local errno capture.
- Normalize libc-style `-1` plus errno or raw negative syscall results into the
  operation and positive errno; a nonzero return is never success. Keep
  interruption distinct. A returning successful exec wrapper is a contract
  violation, not `execSucceeded`.
- Invoke direct `execve` once with prepared NUL-terminated strings/pointers and
  an absolute path. Keep loader, argv/environment, executable identity, and
  their lifetimes explicit; there is no PATH search or shell fallback.
- Account for implicit native runtime/FFI calls as well as authored calls when
  refining the post-install boundary. Source adjacency alone does not establish
  that no intervening syscall occurs.
- Establish [§FS-filter-loading.installation.entry](../functional-spec/FS-filter-loading.md#installationentry-entry-conditions-and-interference) and current-thread attachment
  and inheritance. External termination/interruption cannot be assumed absent.
- Any future input-FD adapter must bound reads, handle short reads/EOF, report
  read/close failures, define cancellation/retries, invalidate owned descriptors,
  and address aliases. The in-memory decoder promises none of this FD behavior.

These are explicit OS/compiler/runtime/FFI contracts under [§FS-assurance.assumptions](../functional-spec/FS-assurance.md#assumptions-initial-assumption-and-obligation-register),
not extra Lean axioms. The M1 binding is implemented and tested under
[§AR-m1-launch.vm](AR-m1-launch.md#vm-disposable-linux-profile-and-evidence); proof of concrete correspondence remains open.
No guest or seccomp experiment runs on the shared host.

## provenance: Source and license boundary

Bubblewrap's source headers identify Alexander Larsson's 2016 copyright and
`LGPL-2.0-or-later`; its pinned `COPYING` contains LGPL 2.1 text. Linux UAPI
headers identify `GPL-2.0 WITH Linux-syscall-note`; retain those notices if any
header/code is later distributed. This slice adds original contracts and Lean
declarations describing published ABI facts; it vendors or translates no upstream
implementation. The root Apache 2.0 license does not relicense those sources.

## obligations: Evidence and next gates

M1.1 evidence is this source map, source identities, compiled declarations, and
reference-fixture checks. M1.2 adds decoder correctness and the executable audit
under [§AR-filter-decoder.audit](AR-filter-decoder.md#audit-declaration-type-and-axiom-gate), with its claim record at [§FS-assurance.decoder](../functional-spec/FS-assurance.md#decoder-m12-decoder-claim-record).
[§FS-assurance.launch](../functional-spec/FS-assurance.md#launch-m13-launch-order-claim-record) adds model launch-order and nonvacuity proofs, while
[§FS-assurance.demo](../functional-spec/FS-assurance.md#demo-m14-isolated-linux-test-record) identifies the test driver/kernel/configuration/platform and
actual observations. Full lifecycle/FD handling, native/Linux correspondence,
confinement, and hardware observations remain open; no production profile is
advertised by these M1 results.
