# DA-m4-effects: Separate byte-aware effects from CompCert compiler traces

For [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and [§AR-m4-effects.machine](../../architecture/AR-m4-effects.md#machine-source-steps-blocked-calls-and-loss), retain the pinned Clight
memory/integer/internal-step semantics and use a separate explicit effect/loss
transition system at external boundaries. Do not encode arbitrary input bytes
as silent or count-only stock external calls: [§AR-m4-native.outcome](../../architecture/AR-m4-native.md#outcome-checked-pure-core-and-rejected-direct-effect-adapter) refutes those
adapters. Merely adding syscall arguments does not prove CompCert trace properties.

The effect layer records bytes and errno updates and admits blocking and loss at
every boundary, including partial transfer without a return. It permits ordinary
short transfers and repeated EINTR without a progress assumption. Unsupported
external functions remain explicit missing semantics. Local contract proofs and
Lean endpoint lemmas are useful independent results, but neither supplies the
full native simulation or the inter-assistant bridge.

This choice does not change upstream CompCert sources or claim preservation of
its compiler theorems for the extension. A later package must prove a suitable
observation/oracle relation or supply a different verified compiler connection.
Linux/libc implementation of each local contract remains a separate obligation.

## primitives: Deterministic reporting routines with loss

For [§AR-m4-effects.errno](../../architecture/AR-m4-effects.md#errno-source-errno-normalization-and-bounded-execution) and
[§AR-m4-effects.readers](../../architecture/AR-m4-effects.md#readers-universal-bounded-frame-reader-execution), use finite certificates of real source steps whose
ordinary successor is unique. Each certificate also classifies every transition
of the unchanged effect/loss machine, retaining asynchronous loss. This lets
finite executions of the read-only reporting primitives establish universal
prefix safety and a bound on execution length. It does not infer universal
safety from one successful test or apply CompCert compiler preservation.

Source constructions accept arbitrary call continuations; universal complete
execution results stop at the local `Kstop` boundary. The caller is outside that
local theorem after return. Stable initialized TLS is explicit for errno, and
nonwrapping readable bytes are explicit for the frame readers. These choices
support [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport); they do not assume publication success or
change the broader reporting contract.

## stores: Preserve bytewise mutation through process loss

For [§AR-m4-effects.writers](../../architecture/AR-m4-effects.md#writers-byte-stores-and-source-codec-round-trips) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), extend the source-certificate
method additively with memory-changing store edges. The original read-only
certificates and effect machine stay fixed. Each new edge proves an actual Clight
step and classifies all machine successors; each finite path carries an invariant
for every intermediate memory. Loss retains that memory, including only the first
written byte. A full-word store is not substituted for the source byte loop.

The public premise is writable byte ownership with no address wrap. A constructed
store chain derives the output and prefix invariant; it is not an assumed successful
execution. Actual allocations, including unaligned addresses, inhabit ownership.
Round-trip proofs first establish exact word identities and then use actual source
calls and memory loads. Caller control flow, C-to-Lean translation and libc/Linux
contracts remain separate obligations.

## library: Version the external boundary and retain arbitrary copy order

For [§AR-m4-library.machine](../../architecture/AR-m4-library.md#machine-additive-external-call-semantics), [§AR-m4-library.memory](../../architecture/AR-m4-library.md#memory-comparisons-strings-and-copying) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), add a
separate library-effect extension. Keep original transitions and theorem meanings
unchanged; explicitly prove reuse at applicable source boundaries. Comparisons
expose arbitrary signed magnitudes with the correct zero/order relation. Copy loss
admits arbitrary bounded destination-byte order, including non-prefix subsets,
because a sequential prefix would exclude common implementation strategies.
Close and exit events describe local calls and source continuation, not OS cleanup
or process-extinction evidence. The new boundary remains a local assumption until
libc/Linux/executable correspondence is independently supplied.

## structures: Keep typed structure copying distinct from initialized byte copying

For [§AR-m4-structures.stores](../../architecture/AR-m4-structures.md#stores-allocation-scalar-stores-copying-and-freeing) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), use Clight's typed
allocation, scalar assignment, complete-object assignment and local freeing.
The result constructor's local structure is 144 bytes; its wire frame is a separate
160-byte layout. Copy actual memory values, including unconstrained padding,
under source alignment and alias rules. The initialized-byte libc `memcpy`
contract cannot justify this structure assignment. A local source copy is one
Clight transition; compiled interruption granularity remains an explicit compiler
observation/refinement obligation. Track all finite source prefixes and free
local storage at actual returns without inventing process-extinction receipts.

## callers: Compose the real helper execution before resuming the caller

For [§AR-m4-callers.continuation](../../architecture/AR-m4-callers.md#continuation-delimited-caller-execution) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), replace only the
callee's bottom continuation and prove this transformation in both directions
for Clight and the extended effect machine. A run either remains in the callee
or reaches a genuine local return and then executes the caller. Preserve memory,
arguments and every event, including unbounded waits/EINTR and partial loss.
No callee postcondition is an external axiom. Apply this to the complete
child-failure routine under [§AR-m4-callers.failure](../../architecture/AR-m4-callers.md#failure-complete-child-failure-reporting); leave the larger frame and
terminal-receiver compositions open. Kernel inventory queries are grouped into
batches of at most 100 declarations, retaining each complete type/assumption
record and the same fail-closed checks and per-command limits.
