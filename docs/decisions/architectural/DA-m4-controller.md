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
