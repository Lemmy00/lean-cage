# AR-verification: Compose explicit refinement and security arguments

To meet [§FS-assurance.closure](../functional-spec/FS-assurance.md#closure-rules-for-stronger-claims), the target chain runs from policy and observations,
through abstract transitions, Lean implementation, compiler/runtime/FFI, and Linux
enforcement, to an identified executable and platform. Every link needs its own
statement, evidence, and assumptions.

## velvet: Imperative proofs in Lean

Use [Velvet](https://github.com/verse-lab/velvet/blob/836ed5a163b36c09081ed1d8aeecd3cec040f87e/README.md)
where its imperative verification approach fits. Keep public contracts and theorem
boundaries in ordinary Lean. Velvet is not a C/Rust-to-Lean translator and does
not establish that hand-translated code matches an upstream binary. Treat its
automation as a producer of terms to check, not an independent trust authority.

## composition: Proof obligations at boundaries

Prove preservation of launch and authority invariants, then connect concrete
effects to abstract steps with explicit failure and interference semantics.
Refinement for safety properties does not automatically yield the confidentiality
property in [§FS-observations.hardware](../functional-spec/FS-observations.md#hardware-software-observable-channels); formulate and prove the needed relation for
the actual observation model.

## audit: Statements, axioms, and nonvacuity

Apply [§REQ-proof-integrity](../requirements/REQ-proof-integrity.md#req-proof-integrity-never-substitute-a-weaker-claim-for-an-unfinished-proof). Audit exported security theorems with their full types
and transitive axioms (for example Lean's `#print axioms`). Reject `sorryAx`
and unapproved compiler-trust axioms, including ones introduced through imported
automation. Require inhabited assumptions and a useful success execution as well
as denied executions. Check liveness separately where it is claimed.

The M0 build only checks that the pinned verification foundation compiles. The
first security theorem must add an explicit axiom audit and claim record; an
empty theorem set does not count as verification.

## artifacts: Bind proofs to releases

Implement a versioned evidence manifest as concrete claims appear, as required by
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record). Reproducible builds identify artifacts but do not prove the
compiler correct. Artifact hashing, conformance tests, and proof checks each
supply different parts of the evidence.
