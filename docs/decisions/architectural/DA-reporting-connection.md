# DA-reporting-connection: Connect reporting through a checked call interface

Under [§AR-reporting.interface](../../architecture/AR-reporting.md#interface-preserve-the-complete-call-observation) and [§FS-workspace.results](../../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), use a whole-call
observation relation between the maintained Clight helper and the ordinary Lean
decoder proof. The source producer supplies the exact frame-field and emitted
prefix equations. The shared normalized publication theorem is an ordinary Lean
proof term rechecked by the strict Rocq importer and consumed by the source proof.
The live Lean consumer connects that same interface to `decodeResult`.

This resolves the selected reporting interface without importing the entire
experimental Clight port. Preserve its separate experiments and the unresolved
general semantics relation. This choice supplies no compiler theorem or Linux
effect producer; those must connect to the actual retained byte-aware semantics
before the executable reporting claim can be completed.
