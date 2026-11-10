# AR-host-boundary: Execute host security control in one shared Lean engine

Implement [§FS-host-boundary](../functional-spec/FS-host-boundary.md#fs-host-boundary-preserve-host-authority-and-bounds-for-arbitrary-vm-bytes) with the native-gateway route in [§DA-host-engine](../decisions/architectural/DA-host-engine.md#da-host-engine-use-a-small-native-python-gateway-and-a-separate-lean-host-image).
The real effect/caller connection precedes isolated parser development.

## organization: Keep one maintained public implementation

`host/` is a responsibility-named Lean package, pinned to the existing toolchain.
It owns `LeanCageHost` and the `leancage-host` executable. Its pure JSON and byte
modules do not depend on workspace policy; M5.3 can reuse them without a package
cycle. Native CPython marshaling belongs in `linux/host_python.c`; individual
Linux effects in `linux/host_primitives.c`. Proofs and source drivers belong in
`verification/host/`. Public Python names ultimately alias the native methods.

Move one live path at a time, preserving useful CLI/library executions during
development. A temporary migration path is not an accepted host proof and must
be removed from the final coverage boundary. Do not retain a second production
snapshot/decoder/publisher or an unchecked plan interpreter.

## interfaces: Fix the data and ownership boundaries before parallel edits

Use namespace `LeanCage.Host`. `Json.Value` represents null, bool, raw JSON number
bytes, decoded strings, arrays and unique-key object lists. `Json.parse` takes
bounded bytes and returns `Except String Value`; `Json.render`, `get?` and
`natural?` serve typed validation. Parsing is total, with explicit byte/depth
bounds, correct UTF-8/escape/surrogate handling and duplicate decoded-key rejection.
Report parsing must not inherit the policy parser's 32-field restriction.

`Transport.Limits` carries stdout/stderr/workspace/inode caps and proves their
supported maxima. `Transport.State` owns identity/header/payload phases, seen
tags, blob counts/bytes and terminal/error state. `step` consumes bounded raw
chunks; `finish` requires terminal plus EOF. It returns raw bounded report,
capture, manifest and blob bytes, not assertions of guest truth. The engine
interprets these exact definitions and derives each chunk bound from its real
read request and primitive reply.

`Snapshot`, `Artifacts`, `Publication` and `Retrieval` use typed paths and retained
directory/handle capabilities. Their executable programs expose each actual
primitive call, result, interruption and loss. Their producers derive fresh
ownership, alias restrictions and byte identities; a path string or receipt
label does not supply those facts. `Host.execute` composes the same programs
used by both public callers and produces the [§FS-host-boundary](../functional-spec/FS-host-boundary.md#fs-host-boundary-preserve-host-authority-and-bounds-for-arbitrary-vm-bytes) acceptance theorem.

The gateway protocol carries exact caller bytes and bounded lengths to one
identified engine. Its C source proof supplies CPython extraction, memory roots,
fixed argv/environment, pipe/spawn ownership, error paths and result projection.
Primitive CPython contracts describe individual API operations. A gateway proof
cannot start by assuming its own extraction or exchange loop succeeded safely.

The received builtin metadata graph stays separate from the customizable output
path presentation. Native `Outcome.observation` exposes that same decoded graph;
`output` records the actual path callback result, while `json()` reflects the
current presentation fields. Source must retain the metadata graph without
passing it to that callback and carry it through allocation and instance storage.
A class-object identity supplies no frozen constructor or path-byte guarantee.
The public result theorem concerns the original return; later caller mutation
and reinitialization remain explicit presentation behavior.
The native type specification sets `Py_TPFLAGS_IMMUTABLETYPE` for `Outcome`, so
ordinary callbacks cannot replace its source-defined descriptors or the actual
instance type. The proof connects that source flag, the allocated type and the
individual CPython lookup rules. It does not freeze instance fields or a path
factory's result.

### interfaces.gateway: Freeze the native request and typed response wire

The request has magic `LCHREQ1\0`, 32-bit command/fault words and eight
`(kind:u32,length:u64)` slots, all little-endian, followed by their payloads in
slot order. The header is 112 bytes. Commands are validate 0, check 1, run 2,
report 3 and bundle 4; faults are none 0, report-storage 1 and channel-loss 2.
Internal CLI command 5 carries each exact OS argv value followed by NUL in the
raw policy slot; empty argv is empty bytes, an empty argument is one NUL. Other
slots are absent except the bootstrap-selected default bundle and optional
explicit package results directory. The total CLI
payload is at most 65536 bytes. The same Lean engine parses it into commands
0–4 and returns typed `exit_code`/`stdout` values to the native CLI projection.
Slots are bundle, results, policy, workspace, stdin, output, timeout and lookup.
Kinds are absent 0, raw bytes 1, OS path 2 and IEEE64 timeout bits 3. Preserve
bytes/path distinctions. Reject wrong command-field combinations and unused
nonempty fields. Policy is at most 65536 bytes, stdin 64 MiB, paths 4095 bytes
without NUL, and a present timeout exactly eight bytes.

The response has `LCHRES1\0`, status/reserved words and a 64-bit length (24-byte
header), bounded payload and EOF. Statuses are success 0, value error 1, OS error 2
and timeout 3. Typed values encode null, boolean, canonical decimal integer,
UTF-8 string, raw bytes, raw OS path, arrays and unique-string-key objects.
Tag 9 carries at most 65536 original JSON-number lexical bytes. The host keeps
these bytes when projecting reports, including unknown numeric fields. Native
decimal integers are constructed in bounded nine-digit chunks, without changing
Python's global conversion limits; fractional/exponent values use the individual
CPython numeric-conversion contract. The CLI emits the original valid token.
JSON input container depth is at most 64. Wire depth is at most 72, allowing the
fixed result/envelope wrappers around any accepted JSON value. Nodes are at most
sixteen times the inode cap and total wire
bytes at most 512 MiB. Per-value lengths are checked before allocation. Native
constructors preserve this typed value; an unchecked pickle, eval or JSON
projection is not the public result connection.

CPython object identity and C reference ownership are separate. Distinct owned
references may point to the same cached object. A source-owned ghost ledger
records the actual temporary, cell or return place that owns each reference;
an actual `Py_DecRef` consumes its operand place. Constructor and `Py_IncRef`
occurrences mint references at their source locations. Ghost instrumentation
must erase to the unchanged physical SDK calls and lift every permitted
physical prefix, including blocked, lost and committed-loss execution. Invalid
ownership actions remain represented; application source proofs must exclude
them on the claimed executions.

## primitives: Enumerate the Linux and runtime effects

The supported CPython configuration uses one interpreter with its GIL and
UTF-8/surrogateescape filesystem encoding. Preparation and actual-caller
acceptance record that configuration. Scalar Unicode conversion uses CPython's
UTF-8 API; OS path conversion uses the configured filesystem API. These are
distinct primitive contracts. The current path/JSON equality claim requires
the stated filesystem configuration; it is not a theorem about arbitrary
interpreter encodings or subinterpreter state.

The native loader boundary supplies individual initialized C regions: actual
source-global symbols, initializer bytes, relocated loads and readable extents.
Empty linked CPython declarations supply no such source initializer. The live
interpreter heap is not equated with standalone `Genv.init_mem`. Source ownership
and retention of each used region remain application obligations.
Read-only source objects have no writable positions in the ELF memory view.
The initialization proof retains descriptor snapshots by restricting its writable
native capability to other objects; a read-only descriptor can still be read.
The individual primitive frames and actual memory permissions establish snapshot
retention. No primitive contract assumes a completed initialization or a frozen
descriptor table across a whole application procedure.

Attached source-only flag cleanup and callback admission use the narrow
`GatewayAttachedNative` interface: ambient retention and actual native stack
allocation/store/free preserve the current attached memory representation.
Pending exceptions remain permitted. These source paths need no SDK callback
frame. The actual public-function entry allocations, global-name lookup and
completed-flag branches are application proofs; a completed-zero callback may
post its error but cannot reach another operational callee, even if its future
return is unavailable. A normal initializer context supplies the same actual
flag cells through its explicit normal-to-attached representation inclusion.

The corresponding storage boundary identifies the native module's C-private
descriptor/literal regions and the named mutable application globals. It grants
writable extents only to actual mutable source globals. CPython-managed module
definitions are excluded from this C-private selection; their SDK updates need
their own primitive contract.
This is an individual ELF mapping/runtime authority contract at load. It supplies
no bootstrap path bytes or later callback frame; the source must establish and
retain each constructed path and each successful-initialization observation.

The two interpreter queries expose the current thread's actual interpreter
pointer and its signed 64-bit identifier. Each query preserves its native
non-output regions, managed heap and source reference pool, and performs no
gateway transport. A held-thread ambient step retains that thread's interpreter
identity. These are individual SDK query contracts. The application passes the
actual first query result to the second, rejects every nonzero identifier, and
owns the initialization flags and all writes to them. Neither SDK query grants
a completed initializer, successful flag or usable class.

Initializer SDK contracts separately describe `PyImport_ImportModule`,
`PyObject_GetAttrString`, `PyModule_Create2`, `PyModule_AddObject` and
`PyModule_AddObjectRef`. A successful import, attribute lookup or module creation
returns one new source reference; cached, immortal and public values may alias.
`AddObject` consumes the caller's selected reference only on success; `AddObjectRef`
retains it on success and failure. The SDK's immediate attribute assignment is
separate from the application proving its call arguments, ordering, selected
reference and final module return. These laws provide no class-global memory
frame, fresh-object claim or frozen public Python object graph. Actual source
assignments publish class roots and archive overwritten unreleased references.

Allocation identities also constrain each individual external, builtin and
ambient memory effect. At a previously valid logical allocation cell, all current
and maximum permissions either survive or are revoked. Byte values may change;
revocation, blocking and loss remain permitted. Reusing a physical address uses
a fresh logical block identity and cannot restore a revoked old lifetime. Actual
source allocation, stores and frees satisfy this representation law separately.
The application proves any required survival from its observed final access;
the law supplies neither a writable stream nor a successful parser result.

Bootstrap uses the actual `dladdr` address and its filename, individual bounded
length/comparison/copy calls and one libc `realpath` resolution. The initialized
bootstrap namespace is protected through that lookup and later exec. Source
checks absolute spelling, suffix, lengths, pointer arithmetic and copy extents
and constructs the actual root, engine and default-results bytes. A loader path
or canonicalization observation is not an already-computed safe bootstrap result.
The `realpath` contract applies to a readable terminated source and a distinct
native destination with the Linux 4096-byte capacity. The source allocation and
loader observations establish their separation. Copy contracts additionally
require the actual disjoint extents; invalid primitive arguments remain broad.

Individual CPython conversions and signal checks may invoke caller callbacks.
Their runtime contracts preserve the actual gateway-owned C cells and IPC
endpoints under the host-code boundary in [§FS-host-boundary.ownership](../functional-spec/FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity).
Callbacks can still reenter and mutate public workspace configuration. The
application must retain roots and copies across those calls; the GIL supplies
neither a buffer-ownership proof nor protection from direct numeric-FD access.
The same host-memory boundary covers private Python graphs. GC tracking can
expose otherwise unpublished containers, so freshness and lack of an ordinary
reference are insufficient by themselves. Per-operation API frames apply only
to actual owned, rooted builtin graphs whose nodes the source has not passed
or published. Callback mutation of public or argument objects remains possible;
deliberate introspection of the private graph is outside the stated profile.

Native access capabilities distinguish real source stack/malloc buffers from
arbitrary writable storage. Retained read-only regions require actual native
ownership or rooted immutable payloads; merely being live does not freeze a
runtime cell. Mutable TLS, reference counts and asynchronous control flags stay
outside those stable regions. Clock, poll and receive operations preserve the
permissions of their actual output spans while writing the specified bytes.
Source allocation, stores and frees transport interpreter roots only across
actual native-private memory operations. They supply no application result or
whole-helper ownership premise.

The thread interface records a held interpreter or the exact detached thread
state returned by `PyEval_SaveThread`. Actual source must connect that token
through the system call and errno capture to `PyEval_RestoreThread`. Treating
the held-GIL predicate as unchanged during this interval would be false.

Native byte observations classify the gateway's actual direct `send` and `recv`
calls, including their descriptor, arguments, returned count and bytes. A
non-transport API event does not assert that callbacks perform no I/O. Their
other effects remain in the backend and interference contracts. Excluding
callback access to this request's channel requires the separately derived
endpoint ownership and the stated host-code boundary; an unpublished descriptor
number does not supply that exclusion.

Native descriptor proofs distinguish the full physical descriptor table from
this invocation's owned leases and shared open-file descriptions. Another thread
can free and reuse an unrelated numeric slot during a libc operation. A returned
fresh socket or duplicate therefore need not have been absent from the whole
table before API entry; it must not replace a protected owned lease. After a
close, the number can already identify a new, unowned object. The close contract
consumes the old lease without asserting global numeric absence. Object and
open-file-description lifetime histories do not reuse logical identities.
Nonblocking state belongs to the shared open-file description; source setup
must establish its actual exclusivity before relying on a flag observation or
update.

Spawn-action and attribute contracts update the actual initialized SDK structs
one operation at a time. Their opaque library allocation footprint stays separate
from source-owned C storage. Application stores must preserve that footprint;
unrelated SDK calls must receive none of its private pointers. Initialization,
each recorded action, attribute update and release retain their actual success
or error result. Initializer laws name the actual separately allocated action
and attribute roots at source offset zero. A scoped registry view supplies no
initializer law for another native address; an arbitrary writable buffer is
not a selected SDK header. Later operations consume the same initialized
pointer and the supported alignment. Application allocation and source argument
proofs produce those bindings, without assuming a globally empty registry.
The shared native-operation bridge sign-extends C `int` operands into the
64-bit word representation; it preserves unsigned 64-bit operands directly.
A libc `-1` return and an actually captured thread errno are distinct inputs
from a POSIX spawn error-number return. Ignored cleanup results do not acquire
a fabricated errno observation. The same live opaque SDK objects supply the
recorded action list and complete attribute snapshot. The application proves
its actual flag/process-group setters; other attribute fields are retained from
that snapshot and are not invented as zero or as inherited process settings.
A selected pending source call can produce its operands before any SDK return,
child creation or successful execution observation.
Its internal spawn observation identifies the same call-entry arguments,
memory and process lifetime and one actual global native row. That observer
requires no enclosing SDK return. Source allocation produces the invocation key
and distinct header lifetimes; source setup produces the four held IPC leases.
The per-operation representation adapter interprets those leases in the full
parent snapshot at the selected fork, permitting unrelated concurrent slots to
differ from SDK entry. `NativeCode.CallRow` preserves canonical full parent
tables/CWD, credentials, optional reply and committed product from that one
`NativeCallAt`. The single fork observation precedes child file actions/exec;
its cloned table/CWD is the parent's table at that actual fork, including SDK
support handles. It is separate from the enclosing SDK's eventual result.

Native pathname metadata operations retain their exact `fchmodat` or `fchownat`
directory, raw pathname, mode or identity words, and flags. A separate resolution
observation names the actual target of that same operation, with the same
process, credentials, before/after worlds, optional reply and committed product.
The directory operand is a lookup base, not the metadata target. This interface
does not replace a pathname setter with an application open followed by an FD
setter, or infer an unchanged private region from a callback summary. Active
parent authority restrictions apply only to the actual resolved setter target;
denied, lost and committed-error observations remain possible.

The spawn primitive copies the supplied path, argument and
environment bytes, recorded actions and the inherited descriptor snapshot into
the same child birth. A birth is not an exec or reaping observation. An actual
exec observation applies those recorded actions and close-on-exec to that child;
application proofs derive the channel layout from the real construction order.
The source spawn runtime's immutable birth/exec views select the actual current
exchange invocation. Its identity comes from the same actor/process incarnation,
function entry and fresh allocated SDK-header lifetimes. The physical adapter
retains every invocation tag in the joint global history and derives the
selected view from those same rows. A source operation's unique new birth does
not exclude unrelated births elsewhere in that history.
The raw engine projection includes only source-owned descriptors 0, 1 and 3;
stderr and SDK references remain separately represented.
The [Linux spawn contract](https://man7.org/linux/man-pages/man3/posix_spawn.3.html)
separates process creation from successful image replacement. The
[duplication](https://man7.org/linux/man-pages/man2/dup.2.html) and
[close](https://man7.org/linux/man-pages/man2/close.2.html) contracts describe the
new descriptor's shared open description and the old slot's possible reuse;
application ownership is still supplied by the source proof.

Authority-metadata frames cover UID, type and low permission/sticky bits only
under actual retained-reference liveness, including references in another actor
or child table. For attribute setters, the application must establish its exact
tracked `user.leancage.*` name. Other attribute names remain in the broad native
relation: POSIX ACL setters can change permission bits, and their byte semantics
are not the tracked user-attribute semantics. A missing raw-table entry does not
establish descriptor invalidity; SDK-owned references have their separate actual
lease contracts.

Error posting has its own rooted interpreter context, which permits a pending
exception. A signal error cannot preserve a clear-pending success predicate.
The individual error API contracts still preserve actual native and immutable
regions and their permissions. Application proofs must carry those owners
through the real failure branch, reference releases and buffer frees; a receipt
for a zero-return read alone does not establish failure-path memory safety.

`Filesystem.Program` interprets the same requests used by source proofs through
`linux/host_primitives.c`. A reply contains a UInt64 status word and owned bytes;
negative errno is represented modulo 2^64. The caller checks success/error,
lengths, narrowing and object ownership. Each dispatch performs one specified
kernel/library operation (or rejects its arguments), not a security procedure.

| Code | Operation and concrete contract |
|---|---|
| 0 | `openat`, exact retained directory, terminated checked bytes, flags and mode; actual descriptor/object and error |
| 1–3 | Bounded `read`/`write`, then individual `close`; actual acknowledged bytes/counts, partial progress and errors |
| 4 | `fstat` on the actual descriptor; eleven exact little-endian UInt64 metadata fields |
| 5–7 | `mkdirat`, `renameat2(RENAME_NOREPLACE)`, `unlinkat`; actual names, identities, atomic nonreplacement and permitted failures |
| 8 | `getrandom` with exact requested count; partial/error outcomes, no assumed application freshness |
| 9–11 | `fdopendir`, `readdir`, `closedir`; the cursor retains and consumes its actual descriptor; bounded observed name/EOF/error |
| 12 | Existing host crypto runtime `SHA256` on the exact immutable input bytes, returning 32 bytes; its computational contract and collision assumption are explicit |
| 13 | `clock_gettime(CLOCK_MONOTONIC)` with exact seconds/nanoseconds; the application constructs and checks deadlines |
| 14 | libc `mkdtemp` on the supplied bounded template; fresh private directory and returned spelling, not a completed run |
| 15 | `geteuid`; the application checks authority/permission observations |
| 16–19 | Nonblocking Unix `socket`, `connect`, bounded `poll` and `getsockopt(SO_ERROR)`; exact descriptors/events/timeout and errno |
| 20–21 | `fsetxattr(XATTR_CREATE)` and bounded `fgetxattr` on the retained publication directory; no pathname reopening |
| 22 | Bounded `getcwd`, preserving actual OS bytes for CLI path association |
| 23 | `kill` on the specified owned process/group with the specified supported signal |
| 24–25 | HMAC-SHA256 of the exact bounded envelope with the private 32-byte key; fixed-time crypto tag comparison |
| 26 | `fcntl(F_SETFD,FD_CLOEXEC)` on the exact inherited IPC descriptor; no close or duplication |
| 27 | `statx(fd,"",AT_EMPTY_PATH)` for exact device/inode/mount identity; unsupported mount identity fails explicitly |
| 28 | Read-only `openat` of kernel `/proc/self/exe`; the protected host procfs binding identifies this process's actual executable object |
| 29 | `fstatfs` on the exact retained descriptor; success returns its filesystem magic as eight little-endian bytes |
| 30 | `ioctl(FS_IOC_GETFLAGS)` on the exact retained descriptor; success returns the actual initialized 32-bit flags as four little-endian bytes |

The checked Lean filesystem adapter lowers each source request to an explicit
primitive program. For [§FS-host-boundary.lookup](../functional-spec/FS-host-boundary.md#lookup-reject-unsupported-directory-name-semantics) it observes filesystem type,
checks ext inode flags, guards relative namespace operands (both rename parents)
and enumeration, and validates each returned directory descriptor. Only tmpfs
or ext without casefold/encryption passes. The C observations make no policy
decision. Lowered executions retain the full raw transcript, including probes,
open-before-rejection, close attempts, interruptions and loss. Completed source
events are a projection of this transcript, not an assertion that an expanded
request was one atomic syscall. The physical connection consumes the same
observed handles. Probe approval names its actual observation snapshot; it does
not freeze foreign-owned input-directory flags. Stable comparison at trusted
write/private-root parents follows their actual authority and the explicit
reconfiguration profile. Broader public input lookup retains flag/name races.

A raw open also records its actual resolved target independently of its optional
acknowledgement. Each resulting raw reference is either an unchanged old
reference or the one descriptor introduced by that same lookup. A lost reply
does not supply a descriptor acknowledgement. Linux reserves the descriptor
slot before path lookup and installs the file afterwards; see `do_sys_openat2`
in the pinned 6.18.59 source and the matching
[upstream ordering](https://github.com/torvalds/linux/blob/v6.18/fs/open.c#L1339-L1364).
These are individual syscall observations, not a frame over a blocked FFI call.
The descriptor-introduction contracts separately record actual open-file-description
lifetime births. A supported source `openat`, `socket` or self-executable open
retains an old exact reference or introduces an actually fresh description,
including a committed operation whose reply is lost. Description lifetimes are
distinct from reused descriptor numbers, inode observations and path-only inode
views. The actual source supplies the supported open flags. These individual
laws allow the proof to trace a current same-endpoint/same-description reference
back to an earlier source boundary, without a whole-channel frame or an
inode-identity injectivity assumption.

Socket queues retain separate actual progress observations indexed by the engine
lifetime and pending raw source ordinal. A still-blocked write can expose several
monotone committed extents; each one appends only its newly committed payload
slice. A later acknowledgement, error or loss reconciles that same occurrence
without appending its bytes again. The source proof derives the exact encoded
response writer at the pending call from the same actor journal. Actual exclusive
file births exclude application file/archive writes on the inherited channel;
the maintained VM-control source excludes its cancellation writes on that same
endpoint and open description. No future engine return supplies this provenance.

The initialized mount view keeps existing aliases and covers. It cannot attach
one of those covers below a directory lifetime born later; the application
proves that lifetime's actual fresh birth. Thus private descendant lookup uses
the stored child under that retained new directory, while public input lookup
still retains its existing mount alternatives and changing name comparisons.
For `close` and `closedir`, every remaining raw reference comes from that same
actor's earlier table. Either call may already have retired its descriptor when
the reply is an error or is lost; no successful acknowledgement or continued
liveness of the closing descriptor is inferred.

The actor journal also records actual process retirement, separately from a lost
source reply. Its kernel row selects the process lifetime and exact surviving
raw references and optional CWD. Partial teardown immediately prevents further
source calls but retains those live resources; only the same actual completed
teardown observation supplies empty resources. The native Python caller uses
its own retirement row and full native resource ledger. Normal native rows keep
other existing caller tables and ongoing teardown tables unchanged; an unrelated
operation cannot erase them as an unobserved process exit. Birth, exec, source,
catalogue and orphan records remain history. The historical CWD identity and
complementary inherited SDK exec snapshot are not claims of continued liveness.
Individual runtime rows still account for their actual SDK leases. These rules
imply neither VM descendant cleanup nor a successful wait/reap observation.

The physical parent receipt starts with the actual guarded open, source UID
check and successful `fstat`, then retains that same object/OFD through every
later row. An active-parent lease contains the genuine earlier source/stat
ordinal and current retained engine reference. Native metadata and comparison
exceptions name the actual syscall and target object, including the same
pathname setter's resolved target; the versioned
host-code profile applies only to an actual reconfiguration of such an active
checked parent. A no-op setter remains possible. Ordinary foreign operations
retain their actual owner/capability checks; permitted public namespace and
content mutations remain in the same history. The application derives current
parent authority and comparison-bit equality from these individual rules.
For a nonempty ext4 boundary, the separate one-operation contract uses the
pinned flag/encryption setter's inode-locked emptiness check. It supplies no
stability claim for an empty directory before its first private binding.

The initialized system-root/`tmp` anchor is separate from these new private
families. Its contract names the original binding, the underlying entry lifetime
and the visible initialized mount object. A single actual `/tmp` open resolves
to that object under the protected initial mount view. The source then supplies
the retained parent reference and the exact generated component. No primitive
asserts that a whole current child pathname belongs to a request. The root-account
case uses the same explicit operator/anchor-reconfiguration exclusion;
unprivileged foreign operations retain their individual DAC obligations.

The pinned Lean handle representation supplies `fileno` on a retained process
stream handle. This adapter performs no read, close or duplication; its borrowed
descriptor remains owned by the rooted handle. The host never combines buffered
reads with raw reads on those streams. Polling uses at most eight descriptors and
at most 100 milliseconds per call. VM diagnostics use these same bounded reads.

The gateway half-closes its data socket after the exact bounded request packet.
The engine checks that EOF before dispatch. A separate fresh inherited socket
endpoint on descriptor 3 carries cancellation; the engine polls it for `C` or parent loss.
Its EOF is a loss observation, never evidence of completed cleanup. The engine
never treats a missing cancellation byte as evidence that the parent is alive
indefinitely.

Before dispatch or child creation, the fresh engine marks inherited descriptors
0, 1 and 3 close-on-exec individually. Failure stops startup. Later process
creation supplies its own explicit stdin/stdout/stderr mappings; it cannot
inherit the engine's private cancellation endpoint. The descriptor remains live
for the engine's own packet/control operations.

All maintained source opens use the actual read/directory/exclusive flags,
including `O_CLOEXEC`; native socket and self-executable opens also set it.
One-syscall reference-origin and close-on-exec laws retain allocations whose
acknowledgement is lost. Individual SDK calls preserve each actual raw lease's
flag while keeping child descriptor tables separate. The selected-spawn proof
extracts that actor's actual earlier launch and startup from the same journal,
then follows the exact source-recorded operations to the spawn. It consumes the
native source's exact socketpair/dup/spawn handoff producer, rather than a free
initial safe table or an assumed already-sealed startup state.

`Entrypoint.run` is the shared executable program for startup, packet input,
command dispatch, the encoded response-size guard and response output. The
executable's `main` interprets that same program. Response output uses bounded
raw writes to its inherited descriptor 1 and advances only by actual partial
acknowledgements. Startup or output failure returns 126; packet failure emits
the typed failure response without calling an application command.

Path arguments are capped at 4095 bytes and checked for NUL before termination.
Reads/writes are capped at 65536 bytes before native copying. The C reply owns
its bytes and captures errno before runtime allocation. Directory cursors require
their actual live ownership token; an arbitrary integer is not a valid pointer.
Loss can occur before a reply, including after a committed primitive effect.

The physical filesystem model distinguishes each object's lifetime identity from
the finite device/inode/mount numbers observed by the application. Allocation
history is monotone for these logical lifetime identities; inode reuse is not
excluded. Each actual syscall has its own before/after objects and reply, and
environment steps can intervene between calls. Other processes cannot alter the
engine's descriptor table. This process-local rule does not freeze input bytes
or shared namespace bindings. Exclusive-open and mkdir freshness are derived
from their individual primitive contracts and actual source calls, including
partial progress and a lost final reply. Directory authority uses the observed
mode, account and sticky-directory checks; account equality alone supplies no
ownership theorem. Same-account concurrent verified callers still require the
application capability/separation producer.

The namespace proof's descriptor map is the actual projection of raw C-owned
handles and inherited IPC capabilities. It excludes stock-runtime handle leases
and internal descriptors; their allocation, rooting, use and finalization have
separate individual runtime contracts. A retained `IO.FS.Handle` supplies the
actual stream/descriptor binding used by VM reads and polls. Absence from the raw
map supplies neither an invalid-descriptor result nor a lease for an arbitrary
integer. OS allocation cannot collide with a live raw reference. Raw references
have no runtime finalizer, and each runtime operation preserves them without
granting a new raw reference. This scope avoids freezing retired stream handles
across response allocation or garbage collection.

The current physical lifetime metadata model uses the supported host-identity
mount profile in [§FS-host-boundary.ownership](../functional-spec/FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity). Its UID/type/mode observation belongs to
that same lifetime across ordinary bind aliases. It does not identify the UID
views of arbitrary idmapped mounts. The application still checks actual stat
and mount-identity observations; those checks do not certify mount UID mappings.
The [Linux 6.8 ID-mapping documentation](https://www.kernel.org/doc/html/v6.8/filesystems/idmappings.html)
explains the distinct ownership and permission views that require this explicit
profile or a more detailed physical model.

A public-handle check accepts only `ENODATA` from the actual retained object's
private-attribute lookup. `EOPNOTSUPP` fails. Unsupported lookup must not be
interpreted as attribute absence on an underlying object reached through an alias.

Permission denial uses the group-class and other mode bits as upper bounds for
all non-owner users, including named-user/group POSIX ACL entries. Missing
membership in the owning group does not establish denial. Private directory
mode masks and supported sticky-parent checks still derive their denials while
permitted public-tree changes remain broad. The host-account syscall contract
names actual effective/filesystem credentials after engine exec and each fresh
mkdir's owner and requested permission mask; later stat checks inspect that same
object. It does not assume a whole private-directory interval remains unchanged.

Foreign namespace observations also retain an object-reference pool covering
ordinary descriptors, in-flight path lookups and transfers among ordinary
processes. A lookup records its actual searched parent and permission check;
an inserted binding records destination write/search checks and a fresh birth,
an existing nondirectory reference, or the source-removal check of a directory
rename. Directory `O_PATH` references remain possible without granting search
or write permission. The application proof derives exclusion of private-file
references and aliases from these individual observations and actual private
births. It does not assume `fs.protected_hardlinks`, freeze foreign public-tree
changes, or treat a current permission mask as a revocation of an older writable
descriptor. The supported profile excludes unauthorized process-memory or
descriptor extraction from the host engine and its owned children; ordinary
UID inequality alone is not such an exclusion.

Host Python callbacks execute with the host account's real filesystem
credentials. Their permitted public filesystem effects require native-caller
operation rows on that same history; they are not ordinary different-UID
interference or owned-child steps. Private pathname/descriptor acquisition by
external host code has the explicit profile boundary in
[§DA-host-engine.hostcode](../decisions/architectural/DA-host-engine.md#hostcode-identify-the-external-host-code-authority-profile). Neither callback scope nor a current permission mask
supplies an application private-family invariant.
Each native operation's namespace record keeps its actual resolved operands,
added/removed stored bindings, acquired references and CWD on that same row,
including committed effects without an acknowledgement. Its primitive laws
contain no private-family label. Profile 1 restricts private acquisition and
destruction on those actual external-code operands; the application must still
derive the private lifetimes, source arguments and concurrent verified callers'
ownership from its creation and removal history. Public namespace changes are
retained rather than replaced by a callback-wide frame.

Protected installation-key markers use the same actual global history. One
native attribute change names its exact set/remove operation, descriptor,
object and attribute name; path authority setters retain their actual resolved
target. The external host-code profile excludes those actual bootstrap-private
acquisition/setter operands. Per-operation metadata/attribute laws and late
reference liveness then derive marker persistence at the snapshot's real
privacy guard. A marker-at-guard or whole-callback preservation assumption is
not an input. The resulting read reference is the same retained object checked
by that guard, including direct and object aliases.

The raw publication receipt retains the exact source-created envelope and the
actual earlier MAC and acknowledged marker operations before its rename. Public
signing queries additionally require the real committed namespace effect and
exposed tag on that output object, regardless of the observed rename reply.
Private precommit tags and internal retrieval MAC computations are excluded
from the public query set. The returned retrieval answer, parsed envelope,
bounded content evidence and real comparison belong to one expanded raw source
transcript. Source-exposure-or-forgery reduction is separate from constructing
the complete custody/key-nonexposure history and from the explicit bounded-game
cryptographic assumption.

The stock Lean runtime's process spawn/read/wait/kill operations have individual
argument/descriptor/process contracts. `Host.Program` exposes their actual
configuration and every return/error branch. It does not assume a whole VM,
controller invocation, cleanup result or host interpreter is correct. Host
bootstrap lookup names remain protected for the request; mutable input and
publication names use their separate retained-object/interference contracts.

Validator observation retains a typed reaping bit from the actual wait result.
A successful wait permits backing-file removal even when policy validation
rejects. Unknown spawn/wait outcomes release raw descriptors while retaining
the reserved name and files. Reusing stdout EOF or a transport error as a reap
observation could free that name while a delayed child still uses its pathname.
The VM spawn-error branch also reports cleanup as unknown and retains its
backing directory. A returned spawn error is not a no-child certificate under
the explicit runtime relation; image/setup failure before spawning is distinct.

Publication releases its raw references after every rename attempt, including an
error acknowledgement. The application does not infer no commit from an errno:
the actual namespace effect and the observed reply are separate primitive facts.
Pre-attempt failures can clean their own stage. No post-attempt branch removes
the old stage name, which another request might reuse after a committed rename.

The extension installation selects the protected engine used for a call, while
the public constructor or CLI can select a bundle. Before dispatch the engine
opens its actual procfs executable, copies through that retained descriptor,
hashes the acknowledged bytes and requires the selected bundle's engine digest.
This preserves bundle selection when the host engine matches and rejects mixed
engine versions before snapshots or VM creation. The procfs lookup has the
explicit Linux self-executable contract and protected host namespace. A path
in the selected manifest does not by itself identify the running engine.

## coverage: Assign every reachable function and real caller

| Current source responsibility | Maintained consumer and proof responsibility |
|---|---|
| `Workspace.__init__`, bundle checks, environment helpers | Engine bundle validation and fixed invocation; gateway constructor/method registration |
| `validate`, `snapshot`, `read_fd`, `path_bytes`, per-run `cpio`/image construction | Request/frozen-byte and snapshot/archive programs; typed bounds before actual effects |
| `Decoder.feed/finish`, `_known_report`, `_validate_result` | Executable transport, total JSON and typed report/artifact validation |
| `parse_export`, `write_exports`, `_publish`, `rename_new` | Checked export plan, directory-relative writes and atomic nonreplacement |
| `Outcome.json`, `report` | Exact native result projection and identity/bounds-preserving retrieval |
| CLI dispatch and Python exports | Fixed native aliases or checked gateway/CLI argument projection |
| VM/socket ownership, cancellation, exit/reap | Working engine/gateway control now; full owned-lifetime producer under [§AR-application-verification.lifetime](AR-application-verification.md#lifetime-owned-descendants-limits-and-cancellation) |

The accepted M5.1 source/worker theorem remains unchanged. Snapshot identity and
input producers feed [§AR-application-verification.authority](AR-application-verification.md#authority-policy-authorized-workspace-construction); observation truth
feeds [§AR-application-verification.composition](AR-application-verification.md#composition-justified-observations-and-the-complete-public-request). Neither is assumed to follow
merely from a valid VM frame.

The verification package under `verification/application` depends on the host
and workspace packages without creating a runtime dependency cycle. Its
`WorkspaceController.lean` is a filesystem alias to the maintained
`workspace/Main.lean`, avoiding the existing core/workspace `Main` module-name
collision. The gate checks that actual source identity. The controller command
proof reads this maintained source directly and kernel-checks its exact
`validate-policy` branch; a copied model or a source hash is not the proof.

## acceptance: Integrate before advertising the guarantee

Begin with the actual public policy caller crossing the native gateway to Lean,
including a rejected request and bounded incomplete response. Prove that prefix
and carry the same implementation through the complete host request. Record
source bindings, complete types/axioms, primitive contracts and input producers.
The final gate includes the affected product checks and one public acceptance
for the final identified bundle, reusing unchanged entry/guest evidence.
