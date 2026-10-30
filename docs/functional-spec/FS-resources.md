# FS-resources: Define and enforce supported resource limits

To meet [§GOAL-native-isolation.outcome](../goals.md#outcome-useful-constrained-execution), a policy may bound memory, process count,
CPU use, and execution duration once the selected profile supports those limits.
Each bound must have a defined unit, enforcement mechanism, and failure behavior.

## limits: Precise semantics

Distinguish instantaneous bounds, cumulative budgets, wall-clock deadlines, and
approximate accounting. Specify scope over descendants and shared resources,
measurement precision, permitted overshoot, and what happens at a limit. Requests
for guarantees the platform cannot supply must be rejected under [§FS-policy.validation](FS-policy.md#validation-reject-unsupported-requests).

## availability: Restricted availability claims

Do not infer host availability or real-time guarantees from a timeout test. State
scheduler, accounting, cleanup, and external-resource assumptions. Liveness and
termination claims require explicit proofs and assumptions in addition to safety.
