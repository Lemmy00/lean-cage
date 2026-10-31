# Architecture

These are design contracts for the staged implementation. M1 supplies a pure
decoder, checked decoder/bounds and launch-order proofs, an axiom audit, a native
Linux driver, and an isolated VM demonstration. M2 adds conditional lifecycle
proofs and a capable VM. M3 adds the useful offline workspace, authority/filter/
resource models and source-bound native tests. Native/Linux correspondence and
end-to-end isolation remain explicit M4/M5 obligations.

| Contract | Subject |
|---|---|
| [§AR-product](AR-product.md#ar-product-one-runnable-product-and-a-composed-assurance-chain) | One maintained executable path, current CLI/VM entry point, integration tasks and release composition |
| [§AR-core](AR-core.md#ar-core-separate-portable-security-contracts-from-platform-mechanisms) | Portable policy, state, effects, and observations |
| [§AR-linux](AR-linux.md#ar-linux-connect-a-lean-launcher-to-real-linux-enforcement) | Linux enforcement, OS bindings, and pinned reference |
| [§AR-filter-slice](AR-filter-slice.md#ar-filter-slice-m11-source-map-and-typed-contract-boundary) | M1.1 source map, ABI, typed contracts, and open binding obligations |
| [§AR-filter-decoder](AR-filter-decoder.md#ar-filter-decoder-byte-decoder-proofs-and-executable-evidence-audit) | M1.2 byte decoder, correctness/bounds proofs, and axiom/evidence gate |
| [§AR-m1-launch](AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration) | M1.3–M1.5 launch proofs, native call map, isolated VM, and evidence review |
| [§AR-lifecycle](AR-lifecycle.md#ar-lifecycle-m2-controller-native-helper-and-evidence) | M2 controller/helper, owned namespace lifecycle, capable VM, proof audit and M4 ledger |
| [§AR-workspace](AR-workspace.md#ar-workspace-m3-authority-model-linux-realization-and-evidence-plan) | M3 runtime lock, object/effect model, native boundaries and acceptance plan |
| [§AR-m4-native](AR-m4-native.md#ar-m4-native-bounded-native-semantics-feasibility-experiment) | M4.1 source-connected feasibility, checked codec executions and rejected direct effect adapters |
| [§AR-m4-effects](AR-m4-effects.md#ar-m4-effects-byte-aware-native-effects-and-asynchronous-loss) | M4.2 partial byte-aware effects, internal Clight/loss product and exact Lean endpoint lemmas; C/Lean/Linux/compiler correspondence remains open |
| [§AR-m4-library](AR-m4-library.md#ar-m4-library-local-library-effects-for-the-reporting-slice) | Local comparison/copy/close/exit effects, preserved earlier source safety and complete fault-selector source connection |
| [§AR-m4-structures](AR-m4-structures.md#ar-m4-structures-local-storage-and-result-construction-in-the-maintained-source) | Actual local/field/storage semantics and complete result constructor source, with loss and caller-memory preservation |
| [§AR-m4-callers](AR-m4-callers.md#ar-m4-callers-actual-source-call-composition) | Actual caller continuation proofs and complete child-failure reporting with bounded byte traces, loss and exit |
| [§AR-m4-decoder](AR-m4-decoder.md#ar-m4-decoder-complete-private-frame-decoding-from-owned-bytes) | Complete private-frame decoder source, exact rejection mutation, all-prefix safety and owned executions |
| [§AR-m4-sender](AR-m4-sender.md#ar-m4-sender-complete-frame-sending-and-publication-return-behavior) | Complete actual frame sending and finish publication/exit behavior, byte-exact outcomes and allocated executions |
| [§AR-verification](AR-verification.md#ar-verification-compose-explicit-refinement-and-security-arguments) | Proof composition, audits, and executable correspondence |
| [§AR-tooling](AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local) | Local tooling, pins, and development checks |
