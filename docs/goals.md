# GOAL-native-isolation: Contain arbitrary native workloads

Following [§GRUND-trust](grund.md#grund-trust-capability-independent-containment-for-ai-agents), provide reusable isolation for malicious native programs,
including code produced by AI agents. Enforcement must not depend on the guest
cooperating, using a particular model API, or being written in Lean.

## outcome: Useful constrained execution

Support a growing, explicit workload and policy subset. The first useful profile
will run a shell and Python in an offline workspace with read-only runtime files,
private writable storage, controlled I/O, and confined descendants.

# GOAL-end-to-end: Connect the policy to the deployed artifact

Following [§GRUND-trust.scope](grund.md#scope-the-destination), connect policy, program semantics, executable code,
OS enforcement, and the deployment profile through reviewed Lean theorems and
explicit foundational assumptions. A proof about a simplified model alone is
not the final result.

## outcome: Auditable claims

For each claim, identify its exact theorem statements, implementation revision,
artifacts, platform requirements, assumptions, and unfinished obligations. Users
must be able to distinguish what is proved from what is tested or assumed.

# GOAL-confidentiality: Account for software-observable leakage

Following [§GRUND-trust.scope](grund.md#scope-the-destination), include functional outputs and software-observable
timing, caches, contention, and speculative execution in the security program.
Physical power/EM measurement and physical tampering are outside this project.

## outcome: Honest profile-specific guarantees

The final claim must name its attacker observations and platform. Restricted
profiles may be necessary; this goal does not assert that arbitrary existing
Linux hardware can provide zero leakage without changes.

# GOAL-reuse: Extend milestones without discarding their foundations

Following [§GRUND-trust.purpose](grund.md#purpose-a-reusable-verification-effort), keep policy, state, observations, and proof
interfaces reusable. New capabilities must preserve existing contracts or
explicitly version them. Use pinned, reproducible tooling and independently
checkable proofs so contributions from increasingly capable agents remain
reviewable.
