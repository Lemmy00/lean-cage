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

## decoder: Derive complete parsing from independent input ownership

For [§AR-m4-decoder.input](../../architecture/AR-m4-decoder.md#input-independent-frame-and-output-ownership), [§AR-m4-decoder.source](../../architecture/AR-m4-decoder.md#source-actual-construction-and-validation) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport),
compose actual short-circuit branches, reader calls, bounded loops and typed
local/output storage. Keep the comparison's complete signed result contract,
waits and process loss. The input contract owns bytes and permissions; validity
and successful execution are conclusions. Preserve the source's output write
before payload validation, including failed decodes with that mutation.

For [§AR-m4-effects.gate](../../architecture/AR-m4-effects.md#gate-additive-evidence-and-completion-boundary), retain fifteen historical caller module names as exact
maintained compatibility sources because their names occur in frozen theorem
types. Audit their whole dependency closure and reject undeclared imports.
Retain the earlier query import context when printing frozen full statements,
so later imports cannot change their name qualification. This fixes replay
reproducibility without replacing the previous propositions or compiled terms.
The additional inventory requires a larger bounded connection replay budget;
per-file compilation, kernel checking, full statements and foundation checks
remain enforced.

## sender: Separate universal source coverage from constructive publication choices

For [§AR-m4-sender.encoding](../../architecture/AR-m4-sender.md#encoding-actual-initialization-copying-and-writer-calls), [§AR-m4-sender.reporting](../../architecture/AR-m4-sender.md#reporting-source-fault-checks-and-complete-writes) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport),
compose actual local allocation, typed structure copying, every zero store,
byte writers, both library copies, ordered fault selectors and complete writes.
Preserve original unsigned kind guards separately from the narrowed wire kind.
Keep selector data outside the TLS error cell because a duplicate report can
perform I/O before later selector reads. Every returning path frees both locals.

The source certificates expose an explicit write-choice parameter. Universal
prefix, progress and exact-return theorems use the unrestricted instance, which
admits all errors and partial transfers. A restricted instance constructs actual
successful histories in the same unrestricted machine; it supports nonvacuity
only. Separate unrestricted certificates construct failed writes and partial
loss. This prevents an existential successful path from replacing hostile-path
coverage. `finish` composes the sender's real execution and preserves its copied
record across all sender effects before the exit mapping, including failed
publication.

For [§AR-m4-effects.gate](../../architecture/AR-m4-effects.md#gate-additive-evidence-and-completion-boundary), retain both preceding theorem-printing contexts, all
680 earlier Rocq records, twelve Lean records and 91 compiled module identities.
Add sender/finish statements and their complete maintained import closure; no
native, extraction, toolchain, Linux or hardware obligation is reclassified.

## receiver: Preserve raw wait status and trace-linked terminal classification

For [§AR-m4-receiver.input](../../architecture/AR-m4-receiver.md#input-independent-caller-memory-and-wrapper-arguments), [§AR-m4-receiver.reads](../../architecture/AR-m4-receiver.md#reads-every-source-read-and-interruption-boundary) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport),
construct the actual seven local allocations from caller ownership and stable
globals. Carry initialized byte prefixes through every read, errno retry and
partial-read loss. The full result is classified from the actual read trace;
finite progress does not assume loop termination. Execute the selected result
constructor, both structure copies and every source free. Close success and
failure both resume the same source continuation.

For [§AR-m4-receiver.classification](../../architecture/AR-m4-receiver.md#classification-exact-raw-wait-and-setup-classification), keep arbitrary wrapper wait words in the
universal theorem. Raw status 65 produces SIGNALLED/detail 65 in a complete
allocated source execution. Adding a 1..64 signal premise here would hide the
upstream provenance obligation. The intended `finish` domain remains explicit;
Linux wait-status correspondence must justify it at composition time.

For [§AR-m4-receiver.evidence](../../architecture/AR-m4-receiver.md#evidence-complete-source-propositions-and-preserved-history), preserve all 875 preceding statements, foundations
and 154 compiled identities, with a separate frozen sender printing context.
The complete 197-module audit receives a bounded 900-second allowance; no check
or source dependency is omitted. Twelve Lean endpoints and every original
native/Linux obligation retain their prior status.

## wire: Compose source observations without assuming Linux provenance

For [§AR-m4-wire.fields](../../architecture/AR-m4-wire.md#fields-recover-the-actual-outgoing-representation), [§AR-m4-wire.private](../../architecture/AR-m4-wire.md#private-exact-private-acceptance-and-rejection-mutation) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), prove
exact field projections of the actual frame, including the source kind-byte
narrowing and private reserved tail. State private acceptance over fields and
retain early versus late rejection mutation. Private ADMITTED/ENTERED records
and the final public Lean result language remain distinct.

For [§AR-m4-wire.composition](../../architecture/AR-m4-wire.md#composition-relate-actual-source-histories-with-explicit-provenance) and [§AR-m4-wire.failure](../../architecture/AR-m4-wire.md#failure-child-failure-words-and-completed-setup-classification), connect actual histories
through explicit observed-byte equality and independent ownership premises.
Disabling the sender's publication fault selector is an input condition, not an
assumption that the decoder accepts. A stored receiver SETUP result, coupled to
an actual child report, implies a complete eight-byte packet and the child's
original bounded stage/error words. Independent allocated executions establish
nonvacuity, including rejected frames, retries and ignored close error.

This source observation relation does not establish Linux delivery, pipe
ownership, interference exclusion or whole-program call ordering. For
[§AR-m4-wire.evidence](../../architecture/AR-m4-wire.md#evidence-additive-source-connections-and-open-bridge), freeze all four previous printing contexts and preserve
1041 earlier Rocq records, twelve Lean records and 197 compiled identities. The
expanded 212-module gate retains the existing 900-second allowance. The checked
Lean bridge and every original correspondence obligation remain open.

## public: Check the live Lean endpoint before bridging proof assistants

For [§AR-m4-public.parser](../../architecture/AR-m4-public.md#parser-both-directions-for-the-live-parser) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), refer to the actual private
M3 parser through a transparent constant alias. The elaborator constructs only
that existing constant reference; the kernel checks the public decoder equality.
No copied parser body, new axiom or trusted computation shortcut supports the
endpoint claims. The original M3 source and public interface remain unchanged.

For [§AR-m4-public.bytes](../../architecture/AR-m4-public.md#bytes-widths-and-independent-encoding), use an independent proof-side frame encoder, exact byte
window lemmas and field-width premises. Prove that the live decoder returns
exactly the live validator on the original record. A width-correct record can
still be semantically rejected. The public kind occupies two bytes and the
private sender narrows its kind to one byte; do not identify those encodings.

For [§AR-m4-public.evidence](../../architecture/AR-m4-public.md#evidence-additive-claims-and-explicit-bridge-boundary), preserve every preceding record and Rocq artifact,
audit the complete maintained Lean source list, and include all generated proof
helpers in the theorem inventory. The public endpoint is a necessary part of a
future checked cross-assistant connection. It does not certify that connection,
Linux transport/provenance or the executable chain.

## bridge: Isolate the strict imported endpoint and prove byte adapters

For [§AR-m4-bridge.normalization](../../architecture/AR-m4-bridge.md#normalization-exact-computational-endpoint) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), remove incidental
string/diagnostic dependencies from the computational decoder without changing
its behavior. Preserve all success fields and exact error messages through an
ordinary Lean equality theorem for every byte array. Import only the computational
root; do not describe its import as an import of that equality proof.

For [§AR-m4-bridge.import](../../architecture/AR-m4-bridge.md#import-checked-terms-and-explicit-logical-model), use a separate Rocq 9.3 profile and a pinned importer
patch that rejects disabled kernel checks. Keep missing-quotient skipping and
parsing-only mode disabled. The imported model uses SProp and definitional UIP;
make its precise foundations visible. Direct import of the original string
closure is currently rejected because the importer's predeclared UInt32 model
is incompatible with Lean 4.35. No unchecked cast or representation assumption
may bypass that rejection.

For [§AR-m4-bridge.bytes](../../architecture/AR-m4-bridge.md#bytes-relate-actual-source-bytes-to-the-imported-reader), prove explicit byte/list/arithmetic conversion and
connect the imported 32-bit and 64-bit reads to the actual C source executions,
including exact unsigned values, unchanged memory, progress and every-prefix
loss. The separate profile rebuilds the original pinned CompCert and all earlier
source modules. Its unsupported-version configuration flag does not disable a
kernel proof check. Translation faithfulness review and complete frame/controller
composition remain separate obligations; this experiment does not close M4.
