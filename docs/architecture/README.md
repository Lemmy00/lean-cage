# Architecture

These are design contracts for the staged implementation. M1 supplies a pure
decoder, checked decoder/bounds and launch-order proofs, an axiom audit, a native
Linux driver, and an isolated VM demonstration. M2 adds conditional lifecycle
proofs and a capable VM. M3 adds the useful offline workspace, authority/filter/
resource models and source-bound native tests. The reusable product now has a
public host/VM workflow. Application correspondence is planned through named M5
deliveries; selected platform and confidentiality proofs are M6 tracks.
Historical proof documents keep their recorded milestone meanings; use the
current roadmap and application-verification contract for assignments.

| Contract | Subject |
|---|---|
| [§AR-product](AR-product.md#ar-product-one-runnable-product-and-a-composed-assurance-chain) | One maintained executable path, current CLI/VM entry point, integration tasks and release composition |
| [§AR-application-verification](AR-application-verification.md#ar-application-verification-prove-the-application-through-integrated-security-guarantees) | Complete application boundary, integrated proof deliveries and current assignment |
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
| [§AR-m4-receiver](AR-m4-receiver.md#ar-m4-receiver-complete-terminal-error-receiver-from-owned-inputs) | Complete terminal-error read loop, raw classification, copies/frees and actual trace bounds |
| [§AR-m4-wire](AR-m4-wire.md#ar-m4-wire-source-connections-through-exact-report-bytes) | Exact report bytes, private field acceptance and connected source histories |
| [§AR-m4-public](AR-m4-public.md#ar-m4-public-exact-live-public-result-endpoint) | Exact live public parser, byte widths and public frame round trips |
| [§AR-m4-bridge](AR-m4-bridge.md#ar-m4-bridge-strict-imported-endpoint-and-source-byte-correspondence) | Strict imported decoder, exact normalization and primitive source-reader correspondence |
| [§AR-m4-controller](AR-m4-controller.md#ar-m4-controller-source-connections-for-controller-inputs-and-ordering) | Exact native decimal parser, aliases, finite-prefix safety and remaining controller ordering |
| [§AR-m4-parent](AR-m4-parent.md#ar-m4-parent-trace-connected-numeric-parent-and-initialization-region) | Reviewed parent composition: actual histories, owned inputs, source cut and complete-region cases; aggregate acceptance recorded separately |
| [§AR-m4-routes](AR-m4-routes.md#ar-m4-routes-early-lean-and-pinned-linux-connection-attempts) | Reproducible strict-import/kernel frontend blockers and required semantics/effect connections |
| [§AR-verification](AR-verification.md#ar-verification-compose-explicit-refinement-and-security-arguments) | Proof composition, audits, and executable correspondence |
| [§AR-tooling](AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local) | Local tooling, pins, and development checks |
| [§AR-reporting](AR-reporting.md#ar-reporting-connect-native-reporting-calls-to-the-live-lean-decoder) | Current complete-helper reporting call connected to the ordinary Lean decoder through checked byte and state observations |
| [§AR-compiled-reporting](AR-compiled-reporting.md#ar-compiled-reporting-carry-reporting-observations-across-verified-compilation) | Concrete verified compilation consumed by the conditional assembly reporting argument |
| [§AR-workspace-vm](AR-workspace-vm.md#ar-workspace-vm-own-the-caller-request-disposable-vm-and-returned-artifacts) | Caller snapshots, private VM transport, cancellation, bundle and source migration |
| [§AR-entry](AR-entry.md#ar-entry-shared-executable-guest-admission-over-primitive-operations) | Shared entry worker and explicit native caller/effect proof obligations |
| [§AR-metadata](AR-metadata.md#ar-metadata-execute-bounded-metadata-control-over-individual-operations) | Shared metadata control and its per-operation handle/state proof |
