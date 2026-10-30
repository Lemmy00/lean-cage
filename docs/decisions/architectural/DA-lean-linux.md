# DA-lean-linux: Build a Lean replacement with Linux as the first backend

**Status: accepted.** Implement selected Bubblewrap behaviors in Lean 4, using
Velvet for suitable imperative proofs, then close the actual Linux and executable
correspondence obligations. This realizes [§AR-linux](../../architecture/AR-linux.md#ar-linux-connect-a-lean-launcher-to-real-linux-enforcement) and [§AR-verification](../../architecture/AR-verification.md#ar-verification-compose-explicit-refinement-and-security-arguments) for
[§FS-launch](../../functional-spec/FS-launch.md#fs-launch-establish-containment-before-executing-the-guest) and [§FS-assurance](../../functional-spec/FS-assurance.md#fs-assurance-bind-every-advertised-guarantee-to-auditable-evidence).

## rationale: Useful work with an expandable proof chain

An existing native Linux sandbox supplies concrete behavior and compatibility
targets. A Lean implementation lets reusable contracts and theorem boundaries grow
alongside the code. The target artifact is the new Lean implementation; certifying
the original Bubblewrap C binary is not a prerequisite.

## consequences: Translation has obligations

Hand translation and differential tests do not prove equivalence. Early results
must expose kernel/compiler/runtime/FFI assumptions. The long-term endpoint still
includes the relevant Linux enforcement chain; replacing it with a permanently
trusted OS contract would change the agreed goal.
