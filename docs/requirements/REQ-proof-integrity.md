# REQ-proof-integrity: Never substitute a weaker claim for an unfinished proof

The assurance goal [§GOAL-end-to-end.outcome](../goals.md#outcome-auditable-claims) and reuse goal [§GOAL-reuse](../goals.md#goal-reuse-extend-milestones-without-discarding-their-foundations) require
honest, reproducible proof boundaries throughout development.

## kernel: Kernel-checked evidence

Security claims must be backed by ordinary Lean theorem terms checked with the
pinned toolchain. No `sorry`, `admit`, `sorryAx`, undocumented axioms, or
compiler-trust shortcuts may support a claimed security result. Inspect transitive
axioms; text searches alone do not establish this. Logical axioms such as choice,
propositional extensionality, and quotient soundness must be declared and reviewed
when they occur, rather than mistaken for new OS assumptions.

## statement: Review the proposition

Review the theorem's full type, hypotheses, quantifiers, and correspondence to the
specification. Do not assume the desired conclusion, make premises inconsistent,
omit hostile transitions, or weaken a contract just to finish a proof. Provide
inhabited models and useful allowed executions to check for vacuity. Distinguish
partial correctness from termination and total correctness.

## provenance: Preserve evidence and scope

Label tests, source mappings, generated code, model proofs, and deployed guarantees
accurately. Generated proof proposals are untrusted until checked. Record upstream
sources and licenses; copied or translated code must retain applicable notices.
Do not use proof length, theorem count, or citation coverage as a security score.

## change: Revalidate affected guarantees

Keep changes bounded, reviewable, and linked to their contracts. Specification
changes must be explicit; dependency changes require impact review. Preserve
unrelated work and active runs. A passing build is necessary but not a substitute
for statement review and artifact correspondence.
