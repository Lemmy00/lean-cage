# DA-m4-controller: Extend source correspondence through small controller routines

For [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request) and [§FS-assurance.native](../../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence), follow the bounded source
connections in [§AR-m4-controller](../../architecture/AR-m4-controller.md#ar-m4-controller-source-connections-for-controller-inputs-and-ordering). Start with the actual decimal parser used by
the helper rather than assuming that plan arguments were parsed correctly.

## decimal: Preserve the actual parser and its aliases

The selected first routine is `number`. Its independent contract in
[§AR-m4-controller.decimal](../../architecture/AR-m4-controller.md#decimal-native-unsigned-decimal-fields) includes the full unsigned range, malformed bytes,
short-circuit overflow rejection and output/input aliasing. Keeping the sole
store after all reads allows an overlapping-buffer theorem without an artificial
separation premise. Input ownership and a writable aligned output remain explicit.

Use a separate extracted AST and module namespace under
[§AR-m4-controller.extraction](../../architecture/AR-m4-controller.md#extraction-independent-controller-slice-and-evidence). Reuse the existing actual Clight step, deterministic
path and loss interfaces. Keep the old reporting AST and proof inventories
unchanged. Use the already pinned isolated Rocq/CompCert profile; introduce no
new checker or native runtime dependency for this routine.

The result remains a source-level parser connection. It does not certify the
Lean-to-native plan encoding, the enclosing controller's call order, Linux or the
deployed executable. Those are the composition work in
[§AR-m4-controller.composition](../../architecture/AR-m4-controller.md#composition-remaining-controller-obligations).

## plan: Normalize the numeric byte interface, preserve the live encoder

For [§AR-m4-controller.plan](../../architecture/AR-m4-controller.md#plan-live-lean-plan-fields-and-their-decimal-bytes), prove facts about the existing
`planArgs`, `Nat.toString` and UTF-8 functions without changing the launcher.
Export a small numeric byte parser whose bound is an explicit argument. Its
computational closure needs natural numbers, lists, booleans and options; it does
not require importing the currently unsupported string/character closure.

The Lean proof connects this interface to the live encoded bytes. The Rocq proof
connects the imported interface to the actual native decimal source. Preserve
both proof-assistant inventories, and keep translation faithfulness separate
from these checked endpoints. Reuse the same pinned strict importer and source
profile, without changing previous proofs or dependency pins.

This slice serves [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request). It does not assume that a valid pure plan
establishes Linux argument ownership, parent identity, policy storage order or
the remaining controller effects.

## main-inputs: Replay against the complete helper translation

For [§AR-m4-controller.main-inputs](../../architecture/AR-m4-controller.md#main-inputs-actual-main-routine-numeric-initialization), use the complete helper's
actual frontend output, including its composite layout and global environment.
Retain the decimal proof sources as the single maintained implementation of
their arguments. Generate a narrowly checked namespace adaptation and local
identifier alias, then kernel-check equality with the complete helper's parser
and replay every original parser proposition and foundation record.

Prove the selected main block from explicit memory ownership, using the existing
Clight transitions and loss model. Stop before invoking unproved failure-report
behavior. Distinguish allocated source witnesses from Linux-supplied arguments;
this serves [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request) while preserving the remaining controller
obligations. Record host-header provenance and licensing without changing the
native implementation, pinned tools or prior proof artifacts.

## bounds: Check the real short-circuit sequence

For [§AR-m4-controller.bounds](../../architecture/AR-m4-controller.md#bounds-actual-policy-bound-validation) and [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request), represent the nineteen
repeated native checks by descriptors and prove their assembled statement is
exactly the selected complete-helper AST. Use those descriptors only after this
kernel-checked identity. Keep the initial argument/byte condition and the final
failure branch as actual source statements, with their machine-width casts.

Reuse the existing source-step, loss and memory interfaces. Require readable
policy values independently, derive that image from successful numeric stores,
and construct finite paths for both acceptance and rejection. This avoids an
assumed execution or policy-validity premise. A selected-block connection does
not establish the preceding checks or the later environment and setup effects.

Normalize the computational Lean interface with explicit field lookup/count and
a structurally recursive, fuelled page remainder. Prove that enough fuel yields
exactly `Nat.mod` and that the complete interface equals the live numeric limits
when the separately checked CPU period is included. The source implementation
continues to use its unchanged unsigned modulus operation.

Direct standard-modulus export, and then a ten-element sparse pattern, brought
division/modulus proof dependencies into the export. The existing strict importer
rejected their `Iff` elimination path. Preserve those experiment receipts and
the strict checker. The normalized computational closure must contain no new
axioms; its ordinary Lean equivalence proofs remain separately audited. This is
a representation connection for [§AR-m4-controller.bounds](../../architecture/AR-m4-controller.md#bounds-actual-policy-bound-validation), not an optimization
or replacement of the running launcher.

## digest: Reuse owned strings for the actual digest recognizer

For [§AR-m4-controller.digest](../../architecture/AR-m4-controller.md#digest-actual-lowercase-digest-text-validation) and [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request), retain the full-program
`digest_text` AST and the existing owned-string `strlen` contract. Prove the
signed-byte tests agree with lowercase ASCII hexadecimal classification, then
construct the source loop and all-execution result. Keep the exact byte predicate
small enough for the unchanged strict importer; connect higher-level Lean
representations through ordinary checked lemmas. No parser or runtime source
change is needed to make this proof convenient.

The local claim is syntax recognition. Caller sequencing, the `none` alternative,
digest verification against content and physical input provenance remain explicit
composition work. Preserve the prior argument-loop checkpoint and its complete
proof and artifact inventory.

## arguments: Preserve waits while connecting length accumulation

For [§AR-m4-controller.arguments](../../architecture/AR-m4-controller.md#arguments-actual-guest-argument-length-accumulation) and [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request), add a local `strlen`
effect over the existing owned C-string representation. Wrap the preceding
library machine without changing its transition relation or its proof artifacts.
Show that internal source steps retain their original meaning and that the
actual `strlen` symbol has exactly the modeled external signature.

Use a finite path certificate that classifies every actual step as the proved
next step, a waiting self-loop, or terminal loss. Measure non-wait steps and
state the selected-block prefix boundary explicitly; the later main routine
must not inherit an unproved invariant. Derive each certificate from independent
table/string ownership and actual source evaluation. The certificate is a proof
output, never an input assumption replacing the source connection.

Prove the accumulator's range before using the later policy-bound block. The
largest signed `argc` and the already-checked 4096-byte per-string bound imply
that the sum of lengths plus NUL bytes fits in unsigned 64 bits. Retain the first
invalid-string ordering and compose the successful total with the existing
policy-bound proofs. Physical argv construction, libc behavior and concurrent
memory interference remain explicit obligations.

Keep the imported argument interface small: a list of natural byte lengths maps
to the per-string acceptance bit and the sum including terminators. Prove the
live Lean array/string projection and fold agree with that interface, then prove
the strictly imported computation agrees with source outcomes. Arrays, Unicode
encoding and physical process memory remain separate layers of this connection;
an accepted length alone must not imply their provenance.

## strings: Preserve library nondeterminism through caller regions

For [§AR-m4-controller.strings](../../architecture/AR-m4-controller.md#strings-actual-caller-string-checks) and [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request), use a branching finite
certificate over the unchanged string machine. A fixed path cannot represent
all conforming `strcmp` return magnitudes. Each certificate node proves ordinary
progress and classifies every actual next step; the local library call keeps
all results allowed by its byte contract. Compose the checked `digest_text`
function at its actual caller continuation.

Permit a region to end at an explicitly identified source state, then split
arbitrary executions at that boundary. This supports selected main blocks
without imposing their read-only invariant on later stores or reporting code.
The certificate is constructed from ownership and the actual AST, never assumed
as an input premise replacing source correctness. Connect original literal
globals through full-program initialization and retain distinct obligations for
physical argv, prior stores and complete main entry.

Normalize the imported byte computation with exhaustive constructor patterns for
both list comparison and the numeric selector. Two sparse-pattern attempts,
including one with an explicit structural recursion annotation, failed strict
import at generated elimination dependencies. Preserve their exact sources,
exports and diagnostic reproductions. Do not relax importer checks; prove the
normalized computation's exact behavior in ordinary Lean and Rocq.

## initialization: Keep sequential stores visible during composition

For [§AR-m4-controller.initialization](../../architecture/AR-m4-controller.md#initialization-actual-flag-and-pointer-initialization) and [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request), reuse the existing
branching region certificate and unchanged string machine. Extend the memory
predicate from equality with one initial memory to the explicit finite sequence
of actual stores. Each source assignment supplies its own ordinary step proof
and classification of every transition. A frame relation preserves all memory
permissions and bytes outside the preflight, export, digest-pointer and
argument-pointer cells. Require separation where subsequent reads need it.

Compose certificates internally and expose an execution guarantee from owned
inputs. The guarantee includes an ordinary path and a split for every finite
execution at its actual source boundary. It does not claim memory preservation
for arbitrary code after that boundary. Constructing a possible later memory
with `Mem.store` only proves that the store is feasible; the reached endpoint
and trace determine whether it was executed. Preserve that distinction on
export, digest and executable rejection and on process loss.
