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
