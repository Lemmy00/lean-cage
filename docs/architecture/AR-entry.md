# AR-entry: Shared executable guest admission over primitive operations

Implement [§FS-entry.control](../functional-spec/FS-entry.md#control-primitive-sequencing-and-failure) and [§FS-entry.check](../functional-spec/FS-entry.md#check-preflight-never-executes-a-workload) with a shared executable Lean
operation sequence and a dedicated Linux entry image. The prepared-root entry
claim is accepted only through the matching source/ordinary records and
integrated checks required by [§AR-entry.acceptance](AR-entry.md#acceptance-required-before-delivery).

## caller: Real launch interface and producer map

The local launch begins at the existing `namespace_init` prepared-root call site,
`namespace_tail 9`, immediately before its guarded `create_entry_child` call.
Its canonical local allocation, argument bytes, filesystem/root and identity
bindings are the named preparation interface supplied by
[§AR-application-verification.authority](AR-application-verification.md#authority-policy-authorized-workspace-construction).
The source invariant is proved at that real statement and environment. It does
not assume the local socketpair, handle aliases, signal action, fork, stop,
placement, publication or release; this delivery proves those operations.
The complete preparation producer must later reach that same statement through
the actual prologue and its error guards. A whole `namespace_init` call is not
currently an executable root in the local-launch machine, because the filesystem
prologue's external operations are outside this slice. Do not use that uninhabited
full-call hypothesis as evidence for the local caller or useful witness.

The public host `Workspace` invokes VM init, which invokes `workspace/Main.lean`;
`LeanCageM3.invoke` supplies `planArgs` to `linux/workspace.c`. The helper allocates
the identity/resources/input/capture objects and clones namespace init.
`namespace_init` constructs the root, creates the private release/failure
socketpair and forks the entry child. Its stop/attach/options/resume/grant
handshake owns admission.

The production entry executable uses `launch/EntryMain.lean`; its separate test
image uses `launch/EntryTestMain.lean`. Distinct module names prevent a dependency's
generic `Main` from being queried in place of the entrypoint. The declaration audit
checks the actual production main-to-worker equation and definition bodies in the
entry package's own compiled import environment.

`create_entry_child` isolates the application control for socketpair,
the private child-end duplicate, signal masking and fork. It receives the three
prepared input/capture descriptors and owned output cells for the parent peer
and child PID. It preserves the original operation and error-capture order;
the child calls `guest` with the same four-handle ABI, while the parent closes
its child-end copy before returning. `namespace_init` closes its remaining input
and capture copies and supplies that returned child to `admit_child`. None of
these multi-operation application functions is a primitive platform contract.
The `release_child` function performs the checked resume and one-byte grant in
that order. Both application functions require complete source proofs. The
actual release caller must first establish that
admission, cgroup-descriptor close and required report publication succeeded.
The release helper cannot supply those caller facts itself.

After the local creation checks and status initialization, namespace init captures
the child PID, parent peer, cgroup descriptor and preflight mode into scalar locals
whose addresses are never taken. Subsequent admission, close, publication,
release and child comparisons use those same values. In the source semantics
they reside in the caller's temporary environment, which a callee cannot change.
The source proof must still establish their initial loads, the private objects
and the actual callback outcomes; it need not invent a whole-callee memory frame
to justify reloading those identities after each helper.

The actual-source caller proof cuts the same finite execution at its first
admission, close, constructor, clock and sender callbacks. It obtains each
standalone callback execution from that wider execution, retaining the original
caller environment and exact source-event intervals. A later release call forces
each earlier callback to return; no callback termination assumption is supplied.
The proof recovers the global forget, result copy and elapsed-time store from
the actual source steps, so a failed assignment cannot silently authorize release.
A finite checked call graph covers the release body and all remaining supervision
source. It excludes another release invocation and any new namespace channel or
descriptor duplicate. The bad latch therefore prevents a later release after any
admission, close, measurement or required publication error. TLS allocation
validity follows the same actual source/primitive execution; exact initialized
errno and whole-callee content frames are not premises for callback ordering.

The child must start the fresh entry image before tracing workload exec. The
handoff preserves exactly the four source handles, root, identity, mode and argv.
The entry program validates aliases, restricts handles and credentials, installs
the exact `LeanCageM3.Filter.bytes`, then performs workload exec (or returns the
separate preflight observation). Their source proofs connect through
[§AR-entry.caller.receipt](AR-entry.md#callerreceipt-required-source-to-public-consumer-mapping); the prepared-object/identity producers belong to
[§AR-application-verification.authority](AR-application-verification.md#authority-policy-authorized-workspace-construction). Supervision and returned observation
producers belong to [§AR-application-verification.lifetime](AR-application-verification.md#lifetime-owned-descendants-limits-and-cancellation) and
[§AR-application-verification.composition](AR-application-verification.md#composition-justified-observations-and-the-complete-public-request).

### caller.values: Connect owned argument bytes to the actual worker

The source image snapshot supplies the complete terminated pointer table and
each string's owned bytes. The runtime argv primitive copies those bytes into
the fresh worker, omits argv zero, and preserves valid UTF-8 bytes. Prepared
root and workload arguments supply the UTF-8 premise; no string identity is
inferred merely from a C pointer. `worker_byte_values` derives the shared
`ArgumentMeaning.byteValues` relation from the maintained worker parser. Import
that relation, its `ArgumentMeaning.nativeValues` producer interface and the
actual unsigned computation strictly into Rocq. On the
same source snapshot, prove its numeric values equal the original UID and
descriptor words, and its root, mode, fault selector and workload bytes equal
the actual copied fields. `worker_native_values` consumes that exact source
certificate in ordinary Lean. Neither an independently selected decoder execution
nor a byte bound supplies this connection.

### caller.pid: Interpret the stopped child's exact PID bytes

The native `admit_child` interface waits for the requested stopped child, bounds
the formatter result to 1–31 bytes, rejects an initial ASCII `0`, and reads the
same owned bytes with the checked native decimal parser. It compares the parsed
value with the actual child PID before writing those bytes to the prepared
`cgroup.procs` descriptor. The formatter's primitive contract supplies bounded
NUL-terminated storage; the application establishes the value and leading-digit
conditions itself. The positive child identity comes from the fork/wait owner,
including its incarnation while stopped and unreaped.

Each check returns immediately on failure. Wait identity and stopped-status
checks precede formatting, so a rejected wait retains that operation's error
state rather than performing an unrelated formatter call first. The public
setup-failure classification is preserved; its error detail now comes from the
last operation actually attempted. After PID validation, a failed placement
prevents option installation, and failed options prevent the helper's successful
return. The supervisor's separate resume check still precedes release.

The leading-digit check matters because the pinned Linux
`kernel/cgroup/cgroup.c:cgroup_procs_write_start` uses
`kstrtoint(strstrip(buf), 0, &pid)`. A leading zero would select octal even though
the native readback parser uses decimal. Successful readback establishes ASCII
digits, and the initial-zero rejection therefore selects decimal in both
interpreters. The parser's width check and comparison establish the exact
positive signed 32-bit PID under [§FS-entry.provenance](../functional-spec/FS-entry.md#provenance-a-return-value-does-not-prove-the-requested-effect-occurred).

The single-write Linux contract for this owned `cgroup.procs` object accepts
the complete bounded decimal buffer, returns the whole requested count after
successful placement, or returns an error. Loss can occur before or after
placement. It does not permit a positive short transfer: `kernfs_fop_write_iter`
rejects overlarge input and incomplete `copy_from_iter` before invoking the
callback; `cgroup_file_write` dispatches to `cgroup_procs_write`, whose successful
return is the supplied count. `write_all` retains its general partial-write
semantics for other objects. This per-object contract is necessary because
separate numeric fragments would be separate cgroup commands. Placement loss
cannot authorize entry: the parent sends the private release byte only after
successful placement and tracer-option installation.

The physical process interface distinguishes a numeric PID from its kernel task
incarnation. The fork snapshot produces the parent/child identity pair; the
application retains an unreaped-child token through the matching stop, numeric
checks, cgroup command and tracer calls. An exit status may reap the child and
permit PID reuse, so the actual status guards must reject that path before
placement. Interrupted waits retain ownership. Killing an unreaped child may
end its execution but cannot recycle its PID.

Individual wait, cgroup-write, SETOPTIONS and CONT contracts use snapshots at
their operation's linearization point. Explicit interference may kill or exit
the child between operations; a late observer does not acquire a claim that the
child is still stopped or alive. The source proof supplies the actual arguments,
the same execution's accepted outcomes and their order. The cgroup object's
authorized run binding remains the named workspace-preparation input.

These are explicit Linux contracts, with source justification rather than a
kernel proof. The source is the Linux 6.18.59 archive pinned by
`tests/vm/bootstrap-pins.json` (commit
`1253a6aa5d104312bf0992afacc15220ae35bdf9`). The inspected files have SHA-256:

| Source | SHA-256 |
|---|---|
| `kernel/cgroup/cgroup.c` | `a7854ee6ff51deb721a69150680645851d99c5daacdb8c779ca9529d5ed0849b` |
| `fs/kernfs/file.c` | `32d8998ea0ffac621b535748f6a327c6e1f126e0f75f4a54b98319b475599cb7` |
| `lib/kstrtox.c` | `5c53d62885e1830fe33a24884343805d2523c6a1b47bed09a2c1bd12a116e1dc` |

### caller.clock: Execute the real clock call before release reporting

The parent reaches release through the maintained `now_ms` and frame sender.
Their successful source paths must execute, including the real `clock_gettime`
call. The clock adapter represents one operation on the caller's fresh 16-byte
`timespec`, with the actual signed 64-bit seconds/nanoseconds fields and a signed
32-bit return. A successful copy may update errno; an error or terminal loss may
leave a partial timespec copy. Those effects frame all other bytes and preserve
the live caller's initialized errno and memory permissions.

The application supplies `CLOCK_MONOTONIC`, checks the return, reads the actual
seconds fields and rejects a negative or overflowing seconds value before
computing milliseconds. Source proofs establish this control and the arithmetic;
the Linux/runtime contract supplies the clock's meaning. The existing zero
fallback represents an unavailable measurement. It does not establish a valid
elapsed-time observation. The actual namespace caller checks the assigned
measurement immediately and latches failure when it is zero, before the sender
and release helper can run. Its production guard remains present when test
injection is disabled; the test build can force a zero after the real clock call.
Public observation provenance remains assigned to
[§AR-application-verification.composition](AR-application-verification.md#composition-justified-observations-and-the-complete-public-request).

### caller.origin: Produce the worker's operation provenance

The caller proof tracks actual global function bindings and the arguments of a
pending native primitive. A statement-only restriction is insufficient: after
the source enters an external `Callstate`, it must retain which request word
the application supplied. The finite program check proves that calls use
global function expressions and that automatic locals do not shadow those
function identifiers. The source invariant preserves that fact across function
entry, calls, returns, labels and the primitive extensions. It derives the
allowed tracer requests for every actual normal or lost ptrace operation and
for a request still pending during waiting. The allowed request log is the
same execution's log, with actual unsigned 32-bit words.

The source cursor advances once per actual next C event. Each consumed occurrence
maps to the same physical tick, actual process snapshots and caller descriptor
table; a reference attached to an unrelated idle tick is insufficient. The
source-table schedule changes only that caller's private table through the
recorded primitive. Other actors frame it under the explicit non-`CLONE_FILES`
descriptor ownership contract. A genuine successful close of its unique writable
cgroup alias therefore removes that object from every later observed caller
table. The actual function allocation supplies local/global/TLS separation; it
is not an assumed whole-helper memory frame.

`CallerRequestsAllowed` is the shared recursive Nat-list predicate. Its strict
import connects the source log to ordinary Lean without changing integer or
list representation in the importer. `CallerControlUse` names the fork-owned
parent/child pair and relates an exclusive tracer's issued requests to that same
source log; detached snapshots are explicit. The per-operation Linux mapping
must produce these uses from the physical task view and actual source history.
It cannot replace that producer with a blanket safe-tracer or kernel-trace
premise. Foreign tracers and intercepted returns remain in the broader runtime
relation.

The process operation relation is indexed by the actual caller identity. A
descriptor number is resolved only in that caller's file table. The local
admission target uses the parent/child fork's PID view; a foreign-namespace
ancestor must supply its actual target resolution or a source certificate that
it issues no debugger operation. Target-independent opcode/payload proofs do
not justify comparing two different PID views.

The process world's cgroup field is the task's retained association. An unreaped
exited task may retain that association until its kernel task is freed. The
successful-image contract separately requires a live task. An association
receipt cannot establish populated scopes or confirmed cleanup; those
observations remain the lifetime delivery's responsibility.

`NamespaceQueue` connects the actual common source prefix to queue birth. Its
single-operation Linux contracts describe the socketpair reset and queue framing
for operations that do not transfer bytes. The certified source log retains I/O
events, and terminal partial transfers cannot reach the live fork frontier. The
application proof therefore establishes empty queues at that same fork, including
when an observation label has been reused. Descriptor absence alone supplies no
queue-initialization fact.

`NamespacePhysical` projects the shared strictly imported physical `Tick` list
into channel events without removing positions. Each tick retains its actual
actor, descriptor object, flags, bytes and source occurrence. File descriptor
words and octets are checked before conversion. Queue provenance returns the
exact earlier send tick and absolute operation ordinal, so the parent source
proof must establish admission and publication for that actual write. The
worker read cut preserves its original table through signals, tracing and stop;
`ChannelExecution.actual_release_read` derives its exact kernel operation from
the ordered native execution. These components remain supporting evidence until
the complete caller and integrated acceptance gate consume them.

`NamespaceGrantCut` starts from an actual parent write on that private endpoint.
It recovers the original captured child and peer through the same source run;
`NamespaceParentSafety` then supplies the checked admission, cgroup close,
nonzero clock and successful publication receipt. Descriptor proofs classify
admission writes as the captured cgroup descriptor and reporting writes as the
immutable report descriptor. The report-only continuation also excludes private
writes after release returns, including the modeled kill and sleep operations.
Thus the selected write belongs to the actual release helper, with an earlier
successful resume and the stored byte 165 at exact source positions. Its Linux
mapping still records every operation by the parent task as an operation of that
same C program; it does not assume that private writes are already authorized.
The valid live TLS block used by the source suffices for the release proof;
the actual ptrace return establishes the errno access needed before the write.

`NamespaceGuestDescriptor` classifies every write by the C guest before the
fresh worker image, including its failure and loss prefixes, as a write on the
original failure socket. Its caller-continuation result uses the source's
proved non-returning behavior. Inheriting a cgroup command descriptor therefore
does not grant this C path an unaccounted placement write.

The global descriptor model starts at that same fresh socketpair birth. Local
close, flags and exec preserve each retained object's descriptor provenance;
dup takes its object from the caller's own table and ordinary open creates an
ordinary object. Fork copying, ancillary-rights send/receive and privileged
descriptor acquisition are explicit operations. The source and worker command
profiles must establish that neither private holder exports a descriptor or
forks again before entry. Prepared ancestor source certificates must exclude
actual privileged acquisition against those holders; root ancestors retain their
real acquisition permission in the kernel relation. Absence from unrelated
tables and pending rights messages is then an inductive result of the actual
operation history, rather than an assumed list of safe table snapshots.

The startup execution keeps the global operation ordinal, physical process
context and entry state together. Its metadata subprogram and native calls may
be interleaved with actual supervisor operations. Each primitive occurrence
maps to that same source-bound kernel journal; erasing the ordinals derives
the caller-control predicates rather than assuming them for a whole helper.
Each returned-operation tick also carries its primitive family, actual opcode
and kernel-origin flag. Native and metadata recordings check this label against
the actual request and origin at that position. Source C primitives carry no
runtime label. Capability adapters consume this same label and the operation's
descriptor observations; equality of context/table observations alone cannot
select an operation with a different opcode or origin.
Metadata operations preserve the task's namespace and cgroup, while the native
contract classifies every write that changes the cgroup as a placement in the
same journal. Ordinary native frames preserve cgroup and namespace; the broader
relation retains writes to arbitrary cgroups. A parent primitive cannot act as
the child calling `TRACEME`. Unsafe tracer contexts also retain arbitrary native
rewriting; the same source-bound journal establishes `ContextSafe` before ruling
out those cases. A supervisor write records its actual C occurrence or a distinct
external actor. Preparation supplies that external actor's lack of writable
cgroup authority. Each cgroup placement is a write to a classified command-file
object in the same tick, with a valid signed descriptor.

These positions are kernel linearization points, not wall-clock intervals from
FFI invocation to return. In particular, a stopped worker's `raise(SIGSTOP)` may
remain pending while the parent places and resumes it. Its stop effect and the
parent operations occupy distinct positions; the later return permits the next
worker operation. A completed-call execution may place intervening supervisor
steps after the stop's linearization and before that next operation. It does not
frame cgroup membership across the whole blocked FFI interval or infer primitive
completion from a stop effect. Pending or lost calls cannot justify a later
worker call or workload replacement.

Successful admission's shared command list excludes native writes. Its actual
execution retains each original return origin: clean initial filters, the
last-position filter command and source-derived safe control justify each
genuine return. Stateful read-only metadata calls preserve clean filters and
cannot write on that same successful path. Thus every write during the checked
worker interval belongs to supervision; source table proofs account for those
writes. The genuine worker `TRACEME` precedes the parent's successful tracer
observation: source-safe kernel steps retain the owned tracer or record a dead
parent, and either state prevents a second successful `TRACEME`. This establishes
that the worker started before the actual cgroup-close checkpoint. Raw source
and external descriptor observations then exclude every placement after that
checkpoint through workload exec. The
successful exec primitive also preserves the physical task incarnation and
scope. Preparation supplies the meaning of the root, leased identity and scope
objects, rather than an already restricted workload state.

The clean-filter producer is a task-indexed lineage of genuine Linux/runtime
operations from clean VM boot through fork and fresh-image exec. Non-fork
operations preserve the process identity in this single-thread entry profile.
The native prctl request is its actual unsigned 32-bit word, bounded below
`2^32`; request 22 is excluded before worker filter installation. A raw syscall
request must be canonical x86-64 below `0x40000000`, excluding the x32 flag and
numbers 101, 157 and 317. Comparing an unbounded Nat with those three constants
would not establish the kernel's effective request. The remaining lineage tags
name internal source steps or declared one-operation runtime adapters; they do
not stand for arbitrary application helpers. The final lineage identity is the
same child used by the returned-operation snapshots.

### caller.receipt: Required source-to-public consumer mapping

The universal source root is the actual prepared `namespace_tail 9` statement.
`NamespacePreparedFork.actual_prepared_source_common_fork_owned` derives the
selected fork's fresh local scope, canonical PID/peer cells, exact continuation
and descriptor log from that execution. It does not receive a fork frontier or
a fork-free transcript. `NamespacePreparedAdmission.actual_prepared_recorded_fork_from_raw`
also derives the original cgroup value through the same common source prefix
and fork copy, then constructs the parent's local storage and separation record.
That record is an internal result. Preparation still supplies the original
root/identity/argument bytes, their permissions, initialized globals, scalar
descriptor values and object authority; it must reach this statement through
the real prologue and error guards in the authority delivery.

The final public consumer must use the actual release read of its successful
`StartupExecution`. `startup_execution_release` supplies that operation and its
position before workload exec. `native_recorded_read` supplies its position,
socket bytes and descriptor table in the same global journal. The original
failure-object observation and actual parser values produce the matching
`TickBinding`. `EntryGuarantee.production_source_workspace` invokes
`SourceScopeProducer` with this exact read and binding, rather than accepting
an unrelated read index, cgroup checkpoint or tracer observation.

`SourceScopeInputs` retains the parent program and source ordinals, the actual
options/close/resume/send/read ticks, the `CONT` action, and their ordering.
The producer exposes placement recordings and source/external descriptor
observations at each position from close through workload exec. These are raw
operation/table facts; the ordinary consumer derives absence of placement and
the final scope from them. An opaque admission predicate, independent safe
snapshots or a whole-interval scope frame cannot replace this interface.

`NamespaceScopeFactory.actual_prepared_source_scope_from_raw` constructs this
producer from the raw prepared caller inputs. It selects the actual parent peer
and child failure descriptor, derives the canonical local input record internally,
and returns `SourceScopeProduction.source_scope_produced`, whose type is exactly
the shared `SourceScopeProducer`. For every actual release read, it joins the
same source fork, child image, capability birth, queue, process schedule and
strictly imported journal. `recorded_source_parent_live` derives parent liveness
through the actual `CONT` from that journal. The parent close proof and child
failure-descriptor proof classify their actual writes; holder writes outside the
recorded C source are checked by the same per-operation origin recording.
Placement samples and foreign cgroup descriptor authority remain explicit raw
runtime/preparation inputs. They do not state admission or scope stability.

The factory also returns `SourceDescriptorOrigin`, retaining the selected
descriptors' actual common-source log, continuation and fork frontier. Callers
use that output to identify the descriptors required by its physical inputs.
For the useful common log, `actual_useful_descriptor_origin` proves parent peer
nine and child failure descriptor sixty. The frontier is produced from the raw
prepared execution.

| Source or recording producer | Result consumed by the public entry proof |
|---|---|
| `actual_prepared_recorded_fork_from_raw`, actual source/queue/capability schedules | One `RecordedForkAdmission` from the selected fork and the actual release read; checked admission/publication and the original parent grant |
| `recorded_grant_actual_admission_source`, `recorded_fork_application_positions` | Actual admission/close intervals, options/close positions, tracer/group observations and close before the same resume/read |
| `recorded_resume_parent_alive_strict`, same-journal request/liveness proofs | Parent liveness through the actual `CONT`; no independent liveness frontier |
| `recorded_fork_public_source_receipt`, `NamespaceScopeBridge.public_scope_inputs` | The exact strictly imported `SourceScopeInputs` record, retaining source references and positions |
| `NamespaceScopeFactory.actual_prepared_source_scope_from_raw` | The complete `SourceScopeProducer` from raw prepared inputs, consumed on the actual native read by `production_source_workspace` |
| `actual_parent_closed_cgroup_write_outside` | Later parent-source writes lack cgroup authority because the real successful close removed its only possible cgroup aliases |
| `actual_same_fork_child_write_outside_cgroup` | Every pre-worker child-source write uses the original failure endpoint, including lost writes; inherited cgroup handles remain modeled |
| Actual metadata/native/supervisor recordings and prepared external authority | Remaining per-position placement and descriptor facts consumed by `production_source_workspace` |

The shared strict export contains the exact Nat/Bool/list receipt definitions.
The source gate records their full types, definition bodies and transitive
assumptions alongside the producer theorems. A name check alone cannot approve
a changed record or weaker producer. The final acceptance also requires a useful
execution inhabiting the same source, queue, capability, metadata/native and
physical history interfaces; separate useful executions do not establish that
composition. `ProcessEntryAcceptance.actual_entry_acceptance` constructs the
closed `EntryAcceptance` record for those same histories and retains equality
with the exact public tick list through
`ProcessEntryTickBridge.entry_runtime_ticks_ordinary`. The canonical gate checks
that witness and the final source/consumer inputs together.

The useful worker's exported descriptor frames retain the actual operation code,
before/after finite slot data and release-read bytes. Ordinary Lean proves that
their reconstructed object/flag functions equal the actual sampled functions on
every descriptor, then proves equality of the complete recorded tick slices.
They share the same strict import as the caller journal, preserving identical
tick, Boolean and task-identity types. The integrated witness must compose the
actual child source, worker startup, actual parent source and worker tail in one
tick list; the source/process, capability and journal proofs must consume that
same list.

The useful image witness ends at the successful kernel image-replacement commit.
With the actual `PTRACE_O_TRACEEXEC` option, the child may then be in its exec
stop; this entry guarantee does not require the new image to have resumed.
Subsequent continuation and lifetime observations belong to
[§AR-application-verification.lifetime](AR-application-verification.md#lifetime-owned-descendants-limits-and-cancellation).

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
| 27 | `read(a,owned-one-byte-output,1)` | Exact one-byte release read; preserve EOF, errors, waiting and loss; the application checks count and byte, and the caller proves the peer's ownership and grant ordering |

The native adapter has compile-time checks for LP64, 32-bit UID/GID widths,
endianness and BPF sizes/offsets. Its source/artifact identity is in the VM record.
The Lean compiler/runtime contract must preserve the borrowed values and the
shared script's effect sequencing. Runtime allocation cannot create a successful
setup reply; runtime termination is loss. Extra runtime memory/clock operations
must preserve the authority projection. No task, process or event-loop API is
permitted in this image. These are precise remaining runtime/platform premises,
not new application lemmas or a trusted admission executor.

The native parent uses fixed-arity declarations in `process_primitives.h` for
`prctl(option,a2,a3,a4,a5)`, `fcntl(fd,F_DUPFD_CLOEXEC,minimum)`,
`rt_sigprocmask(SIG_SETMASK,&mask,NULL,8)`, a default `rt_sigaction`, and
`ptrace(request,child,address,data)`. Each implementation forwards one operation
and its actual return/errno. The handoff's `entry_descriptor_flags(fd,flags)`
similarly denotes one `fcntl(fd,F_SETFD,flags)`. These declarations expose exact
argument lists in the source semantics: variadic libc declarations with omitted
extra argument types would make the pinned Clight call rule inapplicable. The
application proof still establishes arguments, ordering and failure control.
The decimal formatter is a fixed-arity adapter for one bounded libc `snprintf`.
Its contract supplies a bounded NUL-terminated string, its exact byte count and
error/memory behavior, without assuming its numeric meaning. Actual source
`number` readback and comparisons establish the UID, handle and child-PID values;
the worker also checks canonical ASCII. The parent writes the checked child PID
through its pre-opened owned
`cgroup.procs` descriptor before enabling continuation; the authority producer
must bind that descriptor to the run's cgroup object. The Linux cgroup interface
parses that write atomically; it cannot consume only a PID prefix as a successful
partial write. Arbitrary interruption/error still prevents continuation.

The executing worker now interprets `Worker.startup`, including the marker and
thread-status guards and original-argv parser. `Startup.AtExec` quantifies over
arbitrary metadata bytes/errors and native returns; `startup_at_exec` derives
the actual selected admission script. A startup read, parse rejection or
unsupported production selector cannot supply a workload-exec path. Metadata
reads use only bounded file reads and cannot dispatch admission operations.
Any exception or runtime loss stops that prefix. The admission state starts
after those reads; its close-range operation removes any inherited high handle.

Successful image replacement is a distinct primitive outcome, with the frame
laws in [§FS-entry.image](../functional-spec/FS-entry.md#image-preserve-authority-across-successful-image-replacement). `admission_image_state` consumes actual body
values and those single-exec laws. It proves the private failure descriptor is
absent and retains the three supplied standard objects, IDs, filter and root.
Post-exec dumpability stays unconstrained, as required by Linux exec semantics.
The pinned kernel source is `fs/exec.c:begin_new_exec` and
`security/commoncap.c:cap_bprm_creds_from_file` in Linux 6.18.59; these describe
platform contracts, rather than verified kernel implementations.

The composed workspace consumer also requires present, classified source
bindings. It proves all three image standard slots contain the same supplied
objects and that slot three is absent. A conditional assertion that every
surviving handle is allowed would permit missing standard slots; it does not
replace this positive supplied-object guarantee. Actual native table bindings
and the loader projection supply presence, while workspace preparation supplies
the descriptor access-mode and object authorization classification. Modes are
indexed by descriptor slot, so aliases of one object may retain different modes.

## acceptance: Required before delivery

Use the full [§AR-application-verification.admission](AR-application-verification.md#admission-fail-closed-native-guest-admission) acceptance, with a theorem
over actual object/credential/filter/argument state, native caller binding,
primitive marshaling audit, useful and failing execution witnesses, exact
type/axiom records and affected disposable-VM/public checks. A successful
prototype or an abstract trace alone does not meet this acceptance.

The integrated gate is `./scripts/check_entry.sh`. It includes the foundation
and public product checks once, the entry executable/type/assumption audit,
the single maintained-source guest/caller/reporting proof graph, preserved
reporting consumers and the final source-bound VM and public-bundle receipts.
Create those receipts by running `python3 scripts/run_m3_vm.py`, building the
public bundle with `./scripts/build.sh`, and running
`python3 tests/product/acceptance.py` on the final relevant inputs. The gate
checks their exact identities and scenario inventory; it does not rerun matching
VM executions. A changed input or failed scenario invalidates the affected
receipt, as required by [§AR-tooling.checks](AR-tooling.md#checks-one-development-gate).

## work: Integrated construction and acceptance

The selected route is [§DA-entry-worker.worker](../decisions/architectural/DA-entry-worker.md#worker-fresh-image-with-a-bounded-runtime-surface).
The maintained construction and its acceptance are:

1. `actual_entry_acceptance` constructs the useful prepared source, both fork
   branches and actual metadata/native worker in one physical history. Source
   cursors, copied memory, queues, capability birth and recorded operations
   refer to that same execution.
2. The universal source producer supplies `production_source_workspace`;
   `CallerWitness.useful_public_source_workspace` consumes the same public
   history, derived native values, scope and actual source labels. Preserve the
   prepared-root authority inputs and every failure/loss case in
   [§AR-entry.caller.receipt](AR-entry.md#callerreceipt-required-source-to-public-consumer-mapping).
3. Review the final producer/consumer types, strict interfaces, primitive laws
   and foundations, then run the canonical maintained-source graph and affected
   entry gate on those final inputs. Preserve the accepted predecessor evidence.
4. Bind the final public bundle and its acceptance receipt. Reuse matching
   source-bound VM evidence; replay only for changed inputs or relevant failures.
   Update the product claim and entry status only after this integrated check.

The strict bridge imports the bounded argument-byte computation, pure caller
records and exact descriptor/tick data. The attempted full-entry import failed
on the pinned `UInt32` representation mismatch; no kernel check was disabled.
Preserve the narrow source/value route. Body/prototype evidence is recorded
separately under [§FS-assurance.entry](../functional-spec/FS-assurance.md#entry-entry-worker-body-and-route-evidence).
