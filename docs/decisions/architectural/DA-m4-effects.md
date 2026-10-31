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
