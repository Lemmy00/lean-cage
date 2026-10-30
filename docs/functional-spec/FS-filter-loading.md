# FS-filter-loading: Prove a small real launch boundary first

The first executable slice serves [§GOAL-end-to-end](../goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact) and [§FS-launch.order](FS-launch.md#order-explicit-lifecycle). It covers
loading a supported syscall-filter representation and installing it before guest
execution, using pinned Bubblewrap behavior as its starting point.

## input: Bytes, bounds, and ABI

Specify byte decoding, instruction layout, byte order, alignment, machine-width
arithmetic, length bounds, narrowing conversions, and the selected architecture
and syscall ABI. Reject malformed, oversized, empty if unsupported, or mismatched
inputs before execution. Do not replace machine integers with unbounded naturals
without proving the conversion obligations. A supported policy-to-filter path
must check the architecture and fail closed on an unsupported ABI.

### input.abi: M1 native x86-64 profile

The first profile is `linux-x86_64-getppid-v1`: Linux x86-64, little-endian,
LP64, with 8-bit bytes, 16-bit `unsigned short`, 32-bit `int` and unsigned
instruction words, and 64-bit pointers and `long`. Its audit architecture is
`0xc000003e`. The input ABI descriptor must match this profile; i386, x32,
big-endian, and other descriptors are unsupported. A descriptor is input metadata,
not evidence that the process or guest actually uses that ABI.

At syscall evaluation, a different audit architecture kills the process. Under
the x86-64 audit architecture, an unsigned syscall word at least `0x40000000`
also kills the process. This rejects x32's marker and negative 32-bit syscall
words. Unknown lower native syscall numbers are permitted by this filter;
their kernel behavior is outside the filter's claim.

### input.layout: Serialized instructions and bounds

Input is one immutable finite byte snapshot, without a header, terminator, or
padding. Each instruction is exactly eight bytes: a little-endian unsigned
16-bit `code` at offsets 0–1, unsigned 8-bit `jt` and `jf` at offsets 2 and 3,
and a little-endian unsigned 32-bit `k` at offsets 4–7. Decode from bytes; the
snapshot need not be aligned and must not be reinterpreted as a native pointer.
For bytes `b0..b7`, the mathematical values are `code = b0 + 256*b1`,
`jt = b2`, `jf = b3`, and `k = b4 + 256*b5 + 65536*b6 + 16777216*b7`.
These formulas specify the values; M1.2 must prove that machine operations
implement them without truncation.

The general instruction ceiling for this slice is 4096 (32768 bytes), below
the 16-bit `sock_fprog.len` ceiling of 65535. The supported form below further
requires exactly nine instructions (72 bytes). Check length and divisibility
before reading fields, allocating native instruction storage, or narrowing a
count. Any conversion from a natural-number byte/index/count calculation to a
machine integer needs a bounds proof in M1.2; wrapping conversions are not
validation. Native pointer layout is a separate binding obligation.

### input.subset: One canonical restrictive filter

Accept exactly this table, including zero unused jump fields. `pc` is zero-based;
conditional targets are `pc + 1 + jt` or `pc + 1 + jf`. Loads are unsigned
32-bit words from `seccomp_data`; comparisons are unsigned. There are no argument
loads, arithmetic, backward jumps, user notifications, or multiple filters.

| pc | code | jt | jf | k | Meaning |
|---|---|---|---|---|---|
| 0 | `0x0020` | 0 | 0 | `0x00000004` | Load audit architecture |
| 1 | `0x0015` | 1 | 0 | `0xc000003e` | Match native x86-64 |
| 2 | `0x0006` | 0 | 0 | `0x80000000` | Kill process on architecture mismatch |
| 3 | `0x0020` | 0 | 0 | `0x00000000` | Load syscall number word |
| 4 | `0x0035` | 0 | 1 | `0x40000000` | Reject words at or above x32 marker |
| 5 | `0x0006` | 0 | 0 | `0x80000000` | Kill process on unsupported syscall ABI |
| 6 | `0x0015` | 0 | 1 | `0x0000006e` | Match native `getppid` (110) |
| 7 | `0x0006` | 0 | 0 | `0x00050001` | Return `EPERM` without executing syscall |
| 8 | `0x0006` | 0 | 0 | `0x7fff0000` | Allow other native syscall words |

This is a filter-loading demonstration profile, not a confinement policy.
Native `getpid` (39), `prctl` (157), `execve` (59), and `exit_group` (231) are
permitted by this filter. The future demonstration must use direct syscalls
for `getpid` and `getppid`, and distinguish raw `-EPERM` from a libc wrapper's
`-1` with `errno = EPERM`. Filter permission alone does not guarantee OS success.

### input.errors: Deterministic rejection and decoder interface

The decoder's target interface takes an ABI descriptor and byte snapshot, and
returns either the single supported program tag or a distinguishable error.
It has no OS effects. Reject in this order:

1. Unsupported ABI descriptor.
2. Empty snapshot.
3. More than 32768 bytes.
4. Byte count not divisible by eight.
5. Instruction count other than nine.
6. First instruction differing from the canonical table, with its zero-based index.

Thus an otherwise well-formed permissive filter, changed jump, swapped byte order,
truncated instruction, or extra instruction is rejected. M1.1 supplies the typed
interface and reference program; M1.2 must implement the decoder, establish
its acceptance/rejection and conversion properties, and test these boundaries.

### input.correctness: Decoder proof boundary

For every ABI descriptor and finite byte snapshot, decoding terminates and
returns exactly one result. Success is equivalent to the descriptor matching
the native profile, exactly 72 input bytes, and each of the nine instructions
satisfying the field equations in [§FS-filter-loading.input.layout](FS-filter-loading.md#inputlayout-serialized-instructions-and-bounds) against the
canonical table in [§FS-filter-loading.input.subset](FS-filter-loading.md#inputsubset-one-canonical-restrictive-filter). The specification predicate
must describe those mathematical byte values, independently of the executable
decoder and its success result.

Prove unsigned 16-bit and 32-bit word reconstruction without truncation for all
possible input bytes. Every executed byte read must have a checked index bound;
prove the accepted instruction count narrows to a 16-bit `sock_fprog.len` without
change and is within the 4096-instruction ceiling. The earliest differing
instruction must be the reported index after all preceding validation checks
pass. No failed case may be silently converted to a supported program.

Supply a concrete accepted snapshot and malformed/boundary tests, including ABI
descriptors, empty/truncated/extra input, both sides of the general size ceiling,
changed opcodes/jumps/constants, and byte order. These are pure decoder results;
theorems about them establish no kernel enforcement, launch ordering, FFI/native
memory layout, or compiler/runtime correspondence. Add a declaration/type/axiom
audit and claim record with the first decoder correctness theorem.

## installation: Success and failure traces

Prove that execution is reachable only after every required restriction and
filter installation succeeds. Cover installation failure and interrupted setup.
For a supported ordered filter list, specify its composition/order before adding
the multi-filter extension; a single-filter subset is sufficient initially.

### installation.entry: Entry conditions and interference

The M1 launch segment starts in a dedicated, trusted, single-threaded child,
before any guest code runs. All unrelated preparation is complete. Its filter
snapshot, native instruction storage, executable path, argv, and environment are
privately owned and stable; there are no concurrent writers, hostile tracers,
shared writable aliases, or inherited user signal handlers that can execute code
or mutate setup state. Existing seccomp filters are unsupported for the initial
demonstration and must be checked in its recorded entry configuration. These are
explicit environment/binding obligations, not facts proved by input validation.

Signals, cancellation, syscall failure, and process termination remain possible.
The launch contract includes those outcomes. It does not cover hostile mutation
that violates the entry conditions, an already running guest, multithreaded
installation, or arbitrary descendant behavior. Those remain later obligations;
they must not be silently excluded from a future full isolation claim.

### installation.states: Launch states and permitted effects

The portable launch contract uses these states and success observations:

| State | Only requested effect | Success observation | Next state |
|---|---|---|---|
| `unvalidated` | Validate the input and profile prerequisites | `validationAccepted` | `ready` |
| `ready` | Set no-new-privileges | `noNewPrivilegesSet` | `privilegesRestricted` |
| `privilegesRestricted` | Install the validated single filter | `filterInstalled` | `filterInstalled` |
| `filterInstalled` | Attempt the prepared executable | `execAttempted` | `executing` |
| `executing` | Await the already attempted exec outcome | `execSucceeded` | `executed` |
| `failed`, `terminated`, `executed` | None within this launch segment | None | Terminal |

Setting no-new-privileges does not drop existing privileges or establish the
broader M2 launch invariant. `execAttempted` records invocation, not guest entry.
`execSucceeded` means image replacement, not a successful return from an exec
binding. All fields and error observations are public in this segment; this is
not a confidentiality model or a termination guarantee.

### installation.effects: OS effects and post-install boundary

The Linux target calls `prctl(PR_SET_NO_NEW_PRIVS, 1UL, 0UL, 0UL, 0UL)`, then
`prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, program, 0UL, 0UL)` for the same
calling thread, then one direct `execve` using a prepared absolute path, argv,
and environment. Installation success means the kernel has attached the exact
validated program to that thread; the program and no-new-privileges persist into
successful exec under the OS contract. No capability-based alternative to
no-new-privileges is supported.

An error-only pipe may be prepared before setup; its child end must be
close-on-exec and may be written only after failure, never between successful
installation and exec. Its ownership, short writes, and failed reporting must
not create an execution path. There is no success-notification write, PATH
search, shell fallback, filter chaining,
or optional setup call between successful installation and the exec attempt.
The target is a trusted, prepared native x86-64 ELF workload for the isolated
demonstration; an ELF/loader check and actual binding are M1.4 obligations.
Fatal diagnostics and process exit after failure remain possible, under the
installed filter. Omitting Bubblewrap's notification and using direct `execve`
are intentional compatibility departures, not claims of source equivalence.

### installation.failure: Terminal failures without rollback claims

Validation rejection enters `failed` with no setup or exec effect. An error from
no-new-privileges, filter installation, or exec enters `failed` and retains the
operation and positive errno in `1..4095`. An unexpected binding return is a
contract violation and also terminal. A raw exec success never returns.
An interrupted syscall is a distinct terminal failure; no automatic retry or
fallback execution is allowed. Cancellation that takes effect before image
replacement is terminal; a cancellation request alone is not completed
cancellation. Resolve cancellation/exec races by their actual completion order.
Process termination ends the segment from any pre-exec state.

Failure, cancellation, or interruption may occur after a restriction has taken
effect: the model must not assert rollback, clear no-new-privileges, or assume a
failed installation left the process unchanged. No transition from `failed` or
`terminated` may attempt guest execution. Error reporting can itself fail or be
interrupted without creating an execution path. A later launch proof must cover
all permitted outcomes, and a separate witness must exhibit successful execution
under inhabited OS premises.

### installation.model: Executable launch semantics and proof obligations

Implement the stage/event transition function and finite trace replay using the
existing portable vocabulary. Include every specified success outcome, operation
error, interrupted call, effective cancellation, contract violation, and external
termination; terminal states have no outgoing setup or guest-execution transition.
The validation verdict must be supplied by actual decoding together with the
profile prerequisite checks. A caller-provided success event is not validation.

Prove that every reachable exec attempt and successful image replacement has
earlier validation, no-new-privileges, and filter-installation receipts, in their
required order. Prove failure absorption and rejection of execution for invalid
input. Supply both an inhabited full success trace and failure traces. These are
partial-correctness results under truthful OS-effect contracts; they do not
assume that all calls succeed, terminate, or are immune to interference.

### installation.binding: First concrete Linux driver

The M1 driver validates the byte snapshot in Lean before entering the native
binding. Prepare immutable path/argv/environment and filter storage before fork.
The dedicated child executes no Lean runtime or allocator work after fork; it
checks the supported entry conditions, resets inherited handlers, establishes
no-new-privileges, installs the exact validated program, and immediately attempts
direct exec. Parent-side waiting/reporting is separate from child setup.

The demonstration target is a prepared static x86-64 ELF executable with a
recorded identity. Preflight must reject unsupported ELF/ABI/interpreter forms;
the trusted profile excludes concurrent modification of that executable and its
inputs. No-new-privileges, install, and exec errors are terminal, including an
error-reporting failure. The driver must distinguish validation, preflight,
operation/errno, signal termination, and guest exit results.

Record the native layout checks and source-to-model call map. Run the allowed
and denied syscall demonstration, malformed inputs, and injected setup failures
only in the disposable recorded Linux profile. A tested call map does not prove
compiler/runtime/FFI or Linux correspondence; those remain explicit assumptions.

## claim: Limited first theorem

Separate decoding/installation correctness from what the installed filter permits.
A well-formed arbitrary filter can allow every syscall. A demonstration must use
an explicitly restrictive policy/filter and show an allowed action succeeding and
a denied action being blocked. At M1, actual kernel enforcement is an assumption;
the demo and the abstract launch theorem do not prove Linux or full isolation.

## reference: Source boundary

Use Bubblewrap v0.13.1, commit `362936aea0d5c6e70f7af75d2d44b5a914cb4ba2`:
[`seccomp_program_new` and `seccomp_programs_apply`](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L245),
plus the no-new-privileges setup and final filter-to-exec path in that file.
Track error exits, the length conversion to `sock_fprog.len`, and operations
between filter installation and `execvp`. This is a source map, not an equivalence
proof or authorization to copy code without preserving its license.
