# DA-host-engine: Use a small native Python gateway and a separate Lean host image

Implement [§AR-host-boundary](../../architecture/AR-host-boundary.md#ar-host-boundary-execute-host-security-control-in-one-shared-lean-engine) for [§FS-host-boundary](../../functional-spec/FS-host-boundary.md#fs-host-boundary-preserve-host-authority-and-bounds-for-arbitrary-vm-bytes). Keep security decisions and
effect sequencing in executable Lean; prove the small C caller/primitive adapters
with the existing actual-source and strict ordinary-Lean bridge.

## decision: Spawn a fresh engine through the stable Python C API

Use a limited-API CPython extension exposing the public native methods. It
copies/roots bounded arguments and calls a separate `leancage-host` executable
through fixed `posix_spawn` arguments and environment. The engine owns snapshots,
VM-byte interpretation, typed validation, publication and retrieval. It has its
own normal Lean runtime initialization. Python does not interpret an effect plan,
and no fork child resumes inherited Lean runtime state.

The operator-selected bootstrap binding includes stable namespace ancestors and
names, not only immutable file contents. `dladdr` supplies a pathname, and a later
spawn/loader lookup must still select that identified object. This is the
protected bootstrap input; caller data/snapshot/publication paths receive no such
assumption. Per-request identity checks remain application proof obligations.

The prototype compiled the actual CPython 3.12 headers with the limited API
`0x030b0000`; the same abi3 object ran under CPython 3.12.3 and 3.13.9. Pin and
record actual SDK/interpreter/ABI inputs. Do not substitute an unsupported
interpreter or private CPython layout behind a generic Python assumption.

## initialization: Guard the complete native module initializer

An ordinary `pathlib.Path` attribute callback can use
`importlib.util.module_from_spec` on the same identified extension and complete
a nested initializer. The bounded caller probe produced different inner/outer
`Outcome` classes without private-memory access or running an engine. Therefore
a blanket C-global frame across that callback is invalid under
[§AR-host-boundary.primitives](../../architecture/AR-host-boundary.md#primitives-enumerate-the-linux-and-runtime-effects) and [§FS-host-boundary.caller.initialization](../../functional-spec/FS-host-boundary.md#callerinitialization-reject-nested-initialization-before-changing-module-state).

Keep the existing initializer body in `host_initialize`. The exported initializer
checks the interpreter first, rejects an active nested initializer, sets its
private guard, invokes that body, clears the guard on every returned outcome,
and returns the same value. A second ordinary probe loaded the same image as
`first._host` and `second._host` after success and received different `Outcome`
classes. Therefore the wrapper also records successful completion permanently
and rejects subsequent direct entries. Ordinary same-name cached Python imports
remain usable; alternate module names do not create independent native state.
The supported main-interpreter GIL serializes guard
access. No callback runs between setting the guard and entering the body, or
between its return and clearing the guard. Sequential retries retain their
existing behavior and explicit earlier reference history before first success.

The source sets the active flag before bootstrap. Carry only the actual loaded
descriptor/literal regions and writable capacities through these source stores
and individual interpreter queries. The bootstrap consumer accepts those derived
current regions; it cannot reassert that every mutable global still contains
its original ELF initializer after the wrapper has changed one.

A public weak-subclass-registry probe retained the actual Workspace,
Cancellation and Outcome classes before `module_from_spec` returned. That
observation does not identify when the native initializer returned. Keep this
timing distinction in its corrected evidence record. The primitive type factory
contract permits callbacks; the application therefore does not assume that a
fresh type is inaccessible until module publication.
Guard the workspace constructor, path conversion, exchange and CLI at entry
with the same successful-initialization flag. Keep each existing function body
as the exact tail after this check so source consumers retain their established
phase definitions. Cancellation and manual Outcome construction use no module
bootstrap or class roots and keep their existing behavior.

## hostcode: Identify the external host-code authority profile

Profile 1 makes the host-code exclusion in
[§FS-host-boundary.ownership](../../functional-spec/FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity) explicit for filesystem access as well as process
memory, raw descriptors and private Python graphs. This is the external caller
boundary used by [§AR-host-boundary.primitives](../../architecture/AR-host-boundary.md#primitives-enumerate-the-linux-and-runtime-effects). A host Python callback runs with
the host account's actual credentials; mode0700 and different-UID VFS denial
cannot justify denying that callback access to a private run or installation
key. Callbacks with arbitrary private host-file authority are outside this
profile. The application API still accepts arbitrary path bytes and aliases
and must prove their validation and use.

Permitted public callback filesystem effects keep their actual operation,
credentials, handles and place in the shared physical history. They are not
classified as an ordinary different-UID peer or an owned child. A callback's
permitted authority is an explicit caller requirement, not a whole-callback
private-state frame. The source proof still produces every private birth,
role, handle and use; this scope decision supplies none of those facts.

The same authority distinction covers publicly named trusted publication
parents. A same-UID callback can chmod such a parent to0777; a different-UID
peer could then legally remove or replace its unmarked stage. UID/mode/ACL/
sticky reconfiguration of an active trusted parent therefore remains excluded
operator/host-account reconfiguration. Permitted public data/name interference
does not grant that authority. The application proof must check the actual
parent and derive its retained authority under these individual operations.

## bootstrap: Keep native aliases and preserve source-package defaults

Public Python modules expose native aliases. The local build installs an ignored
extension symlink in the repository's Python package; portable bundles contain
the actual extension in the same package layout. Native bootstrap retains the
original loader pathname for that package's default results directory, and uses
checked `realpath` plus the fixed package suffix to identify the canonical
bundle/engine. Both lookup chains have the protected bootstrap contract.

Thus repository imports retain the repository's `.tools/product/runs` default,
and installed imports retain the installation's default. The native CLI sends
that explicit default in its existing results slot; the Lean CLI parser may
override it with the caller's `--results`. No mutable hidden configurator or
per-request Python plan interpreter is introduced. Library `results=None` uses
the same package default. Caller data paths retain their separate lookup rules.

## evidence: Settle the real native-source connection early

The isolated experiment at `.tools/host/prototype` exercised an actual native
`Workspace.run` method, exact binary policy/Unicode path and maximum-size
round trips, fragmented/truncated/oversized/trailing responses and concurrent
calls. The pinned Clight frontend accepted the actual Python/process headers.
Source and strict imported Lean decisions have independently kernel-checked
accepted argument, error-return and method-registration connections.

That experiment does not establish the complete CPython extraction prefix,
exchange loop, engine control, public caller or host guarantee. Carry those
through the maintained implementation and full [§FS-host-boundary.acceptance](../../functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation);
the feasibility experiment is supporting work within the delivery.

## consequences: Keep exact ABI, memory, signals and ownership visible

Use individual immutable-buffer, tuple/keyword, constructor/reference and GIL
contracts, with actual C branches/memory proving their composition. Strong roots
or copied storage survive released-GIL intervals. Periodically dispatch Python
signals or route CLI signals natively; indefinitely releasing the GIL does not
run main-thread Python handlers. An owned cancellation pipe/event supplies a
request, never an assumed completed teardown.

Separate engine initialization avoids embedding Lean's task manager/TLS in
arbitrary CPython threads. Engine and QEMU ownership compose across failures and
loss under the assigned lifetime delivery. Keep that interface concrete now;
do not postpone a new language-semantics project or hide a multi-operation native
executor behind a primitive assumption.

## presentation: Retain received metadata independently of path callbacks

For [§FS-host-boundary.caller](../../functional-spec/FS-host-boundary.md#caller-preserve-the-public-request-and-result-interfaces), keep the original builtin engine metadata
graph in the native outcome and expose it as read-only `Outcome.observation`.
The attribute does not make the returned graph immutable: the application
guarantee concerns its value at the original workspace return. A manual or
reinitialized outcome without received metadata returns `None` there.

The output field retains its existing captured-path-constructor callback;
`json()` retains current-field rendering. A captured class identity cannot freeze
`__new__`, and the callback may return a publicly aliased mutable value. Checking
that value would provide only a sample before later callbacks. Keeping the
received graph separate preserves the lossless output spelling without a path
factory assumption or a replacement path API. Under
[§AR-host-boundary.interfaces](../../architecture/AR-host-boundary.md#interfaces-fix-the-data-and-ownership-boundaries-before-parallel-edits), the source proof retains the actual graph and
roots and proves it was never a callback argument. Neither view supplies
publication authority.

Create the native `Outcome` heap type with `Py_TPFLAGS_IMMUTABLETYPE`. Otherwise
the same path callback could replace the public observation descriptor before
the result returns, defeating the new consumer despite correct hidden storage.
The flag protects class slots and descriptors and prevents instance-class
replacement; it leaves the maintained instance setters and explicit initializer
available. The application produces the actual flag in its type specification
and uses the individual CPython type/lookup contract. A private C class pointer
alone supplies neither this flag nor an attribute-dispatch guarantee.

## extraction: Execute fixed-argument keyword parsing in the checked source

The pinned Clight call rule evaluates a fixed list of formal argument types;
it cannot execute the variable argument tail of `PyArg_ParseTupleAndKeywords`.
The initial frontend acceptance therefore did not settle the extraction prefix.
Replace that use with a maintained parser with fixed arguments for the current
object-only signatures. Its actual branches and loops establish positional and
keyword selection, required/default and keyword-only behavior, duplicates and
errors. Individual tuple, dictionary and genuine Unicode SDK operations supply
their ordinary object operations. Retain selected arguments before any
callback-capable conversion. Exercise public call-shape parity and the same
mutable-keyword-dictionary ownership regression before changing the canonical
source and refreshing its dependent evidence.

The same source audit replaces all reachable variadic object/method calls with
actual fresh tuple construction and fixed-argument calls. Allocation, reference
transfer, callback exceptions and releases belong to their application proofs.
`linux/host_python_primitives.c` gives `fcntl` a fixed three-argument ABI and
forwards exactly that one Linux operation. The explicit native ABI contract
covers this adapter; it performs no setup sequence or application decision.
Both its source and header are identified alongside the caller and linked into
the same bundle. Unused variadic SDK declarations authorize no executed call.

## publication: Prepare a marker and prove its final namespace binding

Use the total bounded parser's decoded-key uniqueness for report, export and
stored-envelope JSON under [§FS-host-boundary.artifacts](../../functional-spec/FS-host-boundary.md#artifacts-validate-all-authority-before-materialization). The previous Python
host decoder accepted repeated keys by keeping the last value. The new host
rejects that ambiguity, including differently escaped spellings of the same
key, before those bytes authorize artifact consistency or retrieval. This is
an explicit accepted-input tightening; ordinary unambiguous version-1 data
retains its format. The existing version-1 policy parser already rejects
duplicates under [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request).

For [§FS-host-boundary.publication](../../functional-spec/FS-host-boundary.md#publication-preserve-observations-through-storage-and-retrieval), prepare the directory marker before atomic
nonreplacement. The typed envelope binds the fresh stage's device/inode, final
parent device/inode and final raw component; the staging component must differ.
Retrieval opens and checks that actual final binding, so a marker in an
uncommitted stage does not authorize a stored result. This keeps attribute
failure before the namespace commit and makes all prepared files visible in
one rename. Lost commit acknowledgement remains uncertain to the original
caller; a later retrieval may observe the committed object directly.

The source/physical join also rejects rollback after a native error return.
The Linux contract permits a committed rename with an uncertain/error outcome,
as illustrated by the [Linux rename documentation](https://man7.org/linux/man-pages/man2/rename.2.html#BUGS).
Deleting through the retained old-stage descriptor could erase committed data;
deleting its old name could remove a peer's newly created stage. Therefore every
post-attempt branch closes its handles only. Pre-attempt failures retain ordinary
owned cleanup, and known reports and public failure status remain unchanged.

An unkeyed attribute cannot authenticate arbitrary preexisting filesystem data.
Authenticate the exact envelope with HMAC-SHA256 under a private, identified
host-only installation key. Its bootstrap ownership/confidentiality, individual
crypto-operation contract and bounded-message unforgeability assumption are
explicit. Application proofs establish which bytes can be signed and published;
they do not assume that an arbitrary matching hash has publisher provenance.
The VM archive never receives this key. Retrieval uses a fixed-time runtime tag
comparison and retains its independent object/name/content/budget checks.

## lookup: Check directory comparison before trusting raw components

The reserved-name and namespace connection in [§AR-host-boundary.primitives](../../architecture/AR-host-boundary.md#primitives-enumerate-the-linux-and-runtime-effects) must
implement [§FS-host-boundary.lookup](../../functional-spec/FS-host-boundary.md#lookup-reject-unsupported-directory-name-semantics). Ext4 can compare different raw names as one
entry when the directory has casefold enabled. That would let an uppercase
spelling enter an unmarked publication stage, and makes different stage/target
bytes insufficient to prove different entries. Reject unsupported directory
semantics through the actual Lean adapter, using separate read-only filesystem
type and inode-flag observations. Support tmpfs and ext without casefold or
encryption; fail closed on unknown filesystems or failed/malformed observations.
Do not hide the policy in a multi-syscall C probe or assume the two names differ.

The pinned [Linux 6.8 ext4 documentation](https://www.kernel.org/doc/html/v6.8/admin-guide/ext4.html#case-insensitive-file-name-lookups)
describes per-directory casefold and name-preserving disk spelling. Linux's
`FS_IOC_GETFLAGS` copies an `int` flag word despite its historical ioctl size
encoding. The adapter uses an initialized 32-bit object and returns exactly four
bytes. Lookup-semantics changes to active trusted write/private-root parents
are explicit operator/host-account reconfiguration. Foreign owners may still
change their own public input directories: a successful probe does not lock
later lookups or establish an interval frame. Keep their actual lookup effects
broad, and derive stable trusted-parent comparison from actual custody. Preserve
all primitive steps and partial/lost prefixes of the checked adapter.

The pinned [ext4 flag setter](https://github.com/gregkh/linux/blob/v6.18.59/fs/ext4/ioctl.c#L621-L635)
and [encryption-policy setter](https://github.com/gregkh/linux/blob/v6.18.59/fs/crypto/policy.c#L547-L555)
also reject the relevant change on a nonempty directory. This supports retaining
comparison semantics once the private boundary binding exists. It does not
establish the earlier probe-to-mkdir interval when a parent was empty. Produce
that interval's trusted UID, retained reference and allowed individual effects
from the actual source. Keep encryption-policy changes as actual native
operations alongside flag changes; do not remove them from public interference.

The [VFS file-attribute wrapper](https://github.com/gregkh/linux/blob/v6.18.59/fs/file_attr.c#L265-L305)
holds the inode lock across the ext4 flag setter, and the encryption-policy
setter holds the same lock across its emptiness check and installation. The
physical contracts therefore distinguish nonempty-boundary persistence from
the earlier active checked-parent interval. The latter is produced from real
source open/stat observations and retained OFD continuity, with per-operation
metadata/flag exceptions bound to their actual target. Host-code reconfiguration
uses the existing profile in [§FS-host-boundary.ownership](../../functional-spec/FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity); it is not inferred from
the caller having a different UID or from a whole callback frame.

## private: Enforce private state through caller paths and actual object checks

The ownership connection for [§FS-host-boundary.ownership](../../functional-spec/FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity) exposed a concrete failure in
the first host integration: a caller could select the host publication key as
stdin, and a caller-selected publication parent could name another request's
temporary stage. The disposable-VM reproduction compares only the selected test
key's digest; it records no raw key. Happy-path roundtrips did not establish the
missing separation.

Reserve `.leancage-private-` components for internal state. All caller data/path
roles traverse retained no-follow ancestors and reject both reserved components
and private object attributes. Check recursively opened snapshot objects too.
Mark the bootstrap key file itself so direct object aliases are rejected. Its
private attribute and contents use the same descriptor. Internal bootstrap reads
remain explicit, rather than treating any host-owned file as private.

Use one fresh reserved directory per request. A shared unmarked anchor could be
left by process loss; adopting it requires unjustified history/alias assumptions,
while rejecting it forever blocks later useful requests. Exclusive creation of
each request's directory supplies a new object without relying on random-name
uniqueness. Publication uses a fresh reserved stage in its destination parent
and makes it public with the single nonreplacement rename. The stage name can
never be the caller's permitted final component.

The child-source connection also exposed unconditional validator cleanup after
an unknown wait. Removing that root could make its old pathname available to a
new request while the first child still runs. Retain the actual wait's typed
reaping observation and remove backing names only after successful wait status;
normal policy rejection still cleans up. Unknown spawn/wait outcomes retain a
private orphan and release the engine's raw handles. This is a namespace custody
decision under [§AR-host-boundary.primitives](../../architecture/AR-host-boundary.md#primitives-enumerate-the-linux-and-runtime-effects), not an inference from EOF or diagnostic text.
Apply the same conservative rule when the VM spawn operation returns an error:
its cleanup is unknown until a genuine no-child/reaping observation is available.
The maintained runtime interface allows a child to commit before an error is
reported. Keeping `not_started` there would authorize unjustified name removal.
Failures before the spawn operation retain the distinct not-started result.

## nativebridge: Bind actual source operands to one native kernel row

For [§FS-host-boundary.caller](../../functional-spec/FS-host-boundary.md#caller-preserve-the-public-request-and-result-interfaces) and [§AR-host-boundary.primitives](../../architecture/AR-host-boundary.md#primitives-enumerate-the-linux-and-runtime-effects), use the exact
shared `NativeCode` operation/reply/product/reference/credential data at the
single Linux or SDK operation boundary. The actual C argument, byte-buffer and
SDK-object producers must supply the encoded operands. The ordinary kernel
consumer keeps the same global row, native process lifetime, credentials and
full parent FD/OFD/CWD snapshots. A source invocation's entry and separately
allocated SDK-header lifetimes stay on its binder. Neither an initialized raw
engine projection nor a later SDK success/birth is an input substitute.

A pending POSIX spawn can create and execute a child before the outer SDK call
returns. Bind its source operands while that real call is pending. Capture the
full inherited table at the actual fork observation; source-held leases identify
only their corresponding entries. Keep committed products independent of an
optional reply and normalize only actually observed C/errno values. The bridge
must construct no application ownership, allowed-policy or complete-result fact.
Application source and kernel proofs retain those obligations.

The bounded direct-import trial strictly loaded the actual executable native
operation decoder. Importing its ordinary word-exactness proof stopped at the
profile's refused unchecked elimination path for `Iff`; importing the full
native row/primitive type stopped at the pinned `UInt32`/`BitVec` representation
mismatch. Preserve those diagnostics in the local native-kernel route evidence.
Keep the existing strict checks and dependency pins. Complete the per-operation
shared-data binder under the explicit Linux/runtime contracts, rather than
making complete actor/compiler import a prerequisite for application behavior.
A matching declaration hash or two passing component builds does not complete
that binder: its actual source-to-row producer and integrated caller remain
required by [§FS-host-boundary.acceptance](../../functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation).

## retirement: Separate process exit from observed resource release

For [§FS-host-boundary.ownership](../../functional-spec/FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity) and [§AR-host-boundary.primitives](../../architecture/AR-host-boundary.md#primitives-enumerate-the-linux-and-runtime-effects), add explicit
engine and native-caller retirement rows to the same global kernel history.
The earlier actor model could stop on a lost source reply but could not express
a later real exit. Keeping its old raw table forever incorrectly made released
handles retain authority and forced nonexistent inode metadata to stay live.
The normal native-call record likewise requires a returned full native table;
it cannot substitute for the Python caller's actual teardown.

An observed exit ends source execution immediately. Its row retains the exact
remaining FD/OFD and optional CWD resources, allowing partial release and a
later completed observation. Normal source calls cannot resume that process
lifetime. Preserve allocated lifetime and catalogue history, immutable exec
provenance and private orphans. Source/kernel metadata laws apply only to
resources or inodes actually still live, with no whole private-region frame.
A completed resource observation concerns that process; descendant supervision
and justified reaping remain separately observed lifetime obligations.
