# AR-entry: Shared executable guest admission over primitive operations

Implement [§FS-entry.control](../functional-spec/FS-entry.md#control-primitive-sequencing-and-failure) and [§FS-entry.check](../functional-spec/FS-entry.md#check-preflight-never-executes-a-workload) with a shared executable Lean
operation sequence and a dedicated Linux entry image. This is work in progress
under [§AR-application-verification.next](AR-application-verification.md#next-first-assignment-and-early-route-decision), not a completed admission claim.

## caller: Real launch interface and producer map

The public host `Workspace` invokes VM init, which invokes `workspace/Main.lean`;
`LeanCageM3.invoke` supplies `planArgs` to `linux/workspace.c`. The helper allocates
the identity/resources/input/capture objects and clones namespace init.
`namespace_init` constructs the root, creates the private failure pipe and forks
the entry child. Its stop/attach/ptrace/resume handshake owns admission.

The child must start the fresh entry image before tracing workload exec. The
handoff preserves exactly the four source handles, root, identity, mode and argv.
The entry program validates aliases, restricts handles and credentials, installs
the exact `LeanCageM3.Filter.bytes`, then performs workload exec (or returns the
separate preflight observation). The native handoff and handshake still require
source proofs; the prepared-object/identity producers belong to
[§AR-application-verification.authority](AR-application-verification.md#authority-policy-authorized-workspace-construction). Supervision and returned observation
producers belong to [§AR-application-verification.lifetime](AR-application-verification.md#lifetime-owned-descendants-limits-and-cancellation) and
[§AR-application-verification.composition](AR-application-verification.md#composition-justified-observations-and-the-complete-public-request).

## effects: Adapter boundary

The native adapter may marshal one concrete operation per request; it cannot
choose subsequent setup steps or invoke a multi-operation admission function.
Record arguments, signed returns/errno, memory bounds/ownership, and Linux
state effects for each operation. The Lean interpreter performs dispatch, return
validation and sequencing. Runtime allocation/initialization failures may stop
execution; they cannot authorize workload entry. The primitive contracts do not
assume confinement, correct caller arguments or truthful reports.

The state records the authority projections consumed by entry: object-valued
handles, all four UID/GID slots, groups, five capability sets, securebits,
dumpability, no-new-privileges, filters, signals, root/cwd and umask. Filesystem
resolution is indexed by the current root and cwd, not only by pathname text.
The prepared-filesystem producer must justify the resolver's stable object
bindings during setup.

`dup2` on the same slot preserves its close-on-exec flag; `dup3` and
`close_range` interpret their actual flag bits. ID reassignment includes the
32-bit `-1` sentinel and Linux's no-op case. `umask` keeps only mode bits.
`prctl` effect reasoning requires the supplied operation code to fit C `int`;
the concrete setup proves that condition. A negative encoded error cannot count
as a successful descriptor-returning operation.

Successful credential operations do not preserve all other credential fields.
The `advance` relation permits collateral dumpability/capability changes, and
the body proof must show that later capset and dumpability operations reset them.
In the pinned Linux source, `kernel/cred.c:commit_creds` may also clear the
parent-death signal. That signal is outside the body-state projection; the local
fork/tracer producer must establish the stop/options/resume ordering, and the
lifetime guarantee must use its actual owned-scope mechanisms.

`PrimitiveContract` is not an implementation correspondence theorem. Its exact
one-operation ABI/memory and Linux frame laws remain enumerated platform/runtime
premises. `KernelTrace` is a separate application caller obligation: raw returned
values from a possible hostile filter or tracer cannot discharge it. The broader
`ReturnedTrace` retains intercepted calls.

The FFI receives a 32-bit operation tag, three 64-bit argument words and borrowed
immutable Lean string/array/byte storage. It returns the raw `BaseIO` tuple,
not an `IO` result wrapper. Negative returns encode a captured errno in
two's-complement form; unexpected return values remain failures. The identified
adapter has the following enumerated runtime contracts:

| Tags | Primitive and exact marshaling | Required effect/ownership boundary |
|---|---|---|
| 0 | `rt_sigprocmask(SIG_SETMASK, &a, NULL, 8)` | Own single-thread signal mask; unmaskable signals are ignored |
| 1 | `rt_sigaction(a, zero kernel action, NULL, 8)` | Default disposition for the supplied supported signal; kernel-sized fields |
| 2–3 | `PTRACE_TRACEME`; `raise(SIGSTOP)` | Exact current child/parent identity and stop/resume semantics; caller proves sole trusted tracer and options |
| 4–6 | `dup2(a,b)`; `dup3(a,b,c)`; `close_range(a,b,c)` | Signed descriptor slots, flag bits, shared object identity and private descriptor-table ownership |
| 7–10 | `chroot(text)`; `chdir(text)`; `setsid()`; `umask(a)` | Borrowed NUL-terminated path, context-indexed object resolution, process identity and masked mode bits |
| 11 | `prctl((int)a,b,c,0,0)` | Exact supported operation/arguments; application proves the operation code fits signed `int` |
| 12–14 | `setgroups(0,NULL)`; `setresgid(a,b,c)`; `setresuid(a,b,c)` | Actual 32-bit ID/sentinel semantics, groups and permitted collateral credential changes |
| 15–16 | `capset`/`capget` with v3 header, PID 0, two three-word capability records or 24-byte output | Current process only; three capability sets and ambient intersection; bounded stack/output memory |
| 17–19 | `getresuid`/`getresgid` with three 4-byte output slots; `getgroups(0,NULL)` | Query current credentials without replacing effects by reported labels |
| 20–21 | `setfsuid(a)`/`setfsgid(a)` | The program uses the all-ones 32-bit sentinel as a non-mutating query |
| 22 | `PR_SET_SECCOMP/FILTER` over a bounded aligned copy of the supplied bytes | At most 4096 eight-byte instructions; x86-64 little-endian layouts; actual filter attachment on genuine success |
| 23 | `execve(text,argv,environment)` | 1–64 borrowed argument strings, eight bounded NUL-delimited environment fields, both pointer tables terminated; successful image replacement has kernel close-on-exec/inheritance semantics |
| 24–26 | `write(a,data,size)`; `exit_group(a)`; `nanosleep(milliseconds)` | Exact byte extent, partial/error returns, non-returning termination or loss; pause is test-only in normal production control |

The native adapter has compile-time checks for LP64, 32-bit UID/GID widths,
endianness and BPF sizes/offsets. Its source/artifact identity is in the VM record.
The Lean compiler/runtime contract must preserve the borrowed values and the
shared script's effect sequencing. Runtime allocation cannot create a successful
setup reply; runtime termination is loss. Extra runtime memory/clock operations
must preserve the authority projection. No task, process or event-loop API is
permitted in this image. These are precise remaining runtime/platform premises,
not new application lemmas or a trusted admission executor.

## acceptance: Required before delivery

Use the full [§AR-application-verification.admission](AR-application-verification.md#admission-fail-closed-native-guest-admission) acceptance, with a theorem
over actual object/credential/filter/argument state, native caller binding,
primitive marshaling audit, useful and failing execution witnesses, exact
type/axiom records and affected disposable-VM/public checks. A successful
prototype or an abstract trace alone does not meet this acceptance.

## work: Remaining integration within the entry delivery

The selected route is [§DA-entry-worker.worker](../decisions/architectural/DA-entry-worker.md#worker-fresh-image-with-a-bounded-runtime-surface). Preserve the public bundle until
the following application connection is checked:

1. Prove the actual native `guest` handoff's argv table, decimal serialization,
   handle preservation, mode guard and failure continuations. Connect those
   owned bytes to `worker_parse_exact`; a bound alone does not prove their value.
2. Prove the relevant `namespace_init` prefix: fresh fork, distinct private
   failure writer, masked signals, the expected child's stop, cgroup attachment,
   sole trusted tracer/options and resume. Include errors, arbitrary waiting and
   loss. Establish the physical origin/context premise for the body theorem and
   the namespace/cgroup/resource projection at exec.
3. Bind the narrow per-operation adapter contracts, exec's close-on-exec effect
   and executable worker identity at those call sites. Keep prepared-root,
   identity and argument storage producers explicit for the authority delivery.
4. Integrate the shared worker into the maintained build/image path, replay
   affected public/setup/preflight cases on the final inputs and consume the
   source-connected entry theorem. Only then update the product claim and mark
   the entry delivery complete.

The strict bridge currently accepts the bounded argument-byte computation. Its
full-entry import failed on the pinned `UInt32` representation mismatch; no
kernel check was disabled. Continue the existing narrow source/value route;
do not restart a general importer project. Body/prototype evidence is recorded
separately under [§FS-assurance.entry](../functional-spec/FS-assurance.md#entry-entry-worker-body-and-route-evidence).
