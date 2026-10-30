# Architecture

These are design contracts for the staged implementation. M1 supplies a pure
decoder, checked decoder/bounds and launch-order proofs, an axiom audit, a native
Linux driver, and an isolated VM demonstration. Native/Linux correspondence and
full workspace isolation remain later obligations. M2 adds conditional lifecycle
proofs, a fresh helper, a capable VM and an explicit M4 obligation ledger.

| Contract | Subject |
|---|---|
| [§AR-core](AR-core.md#ar-core-separate-portable-security-contracts-from-platform-mechanisms) | Portable policy, state, effects, and observations |
| [§AR-linux](AR-linux.md#ar-linux-connect-a-lean-launcher-to-real-linux-enforcement) | Linux enforcement, OS bindings, and pinned reference |
| [§AR-filter-slice](AR-filter-slice.md#ar-filter-slice-m11-source-map-and-typed-contract-boundary) | M1.1 source map, ABI, typed contracts, and open binding obligations |
| [§AR-filter-decoder](AR-filter-decoder.md#ar-filter-decoder-byte-decoder-proofs-and-executable-evidence-audit) | M1.2 byte decoder, correctness/bounds proofs, and axiom/evidence gate |
| [§AR-m1-launch](AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration) | M1.3–M1.5 launch proofs, native call map, isolated VM, and evidence review |
| [§AR-lifecycle](AR-lifecycle.md#ar-lifecycle-m2-controller-native-helper-and-evidence) | M2 controller/helper, owned namespace lifecycle, capable VM, proof audit and M4 ledger |
| [§AR-verification](AR-verification.md#ar-verification-compose-explicit-refinement-and-security-arguments) | Proof composition, audits, and executable correspondence |
| [§AR-tooling](AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local) | Local tooling, pins, and development checks |
