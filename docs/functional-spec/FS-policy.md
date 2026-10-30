# FS-policy: Grant only explicit, supported authority

To meet [§GOAL-native-isolation](../goals.md#goal-native-isolation-contain-arbitrary-native-workloads), every launch must use an explicit policy describing
which resources and operations the guest may access. The operator selects the
policy; the guest is untrusted even if an agent also helped author that policy.

## authority: Resources and permitted operations

Model rights over objects, handles, processes, and namespaces. Access not granted
by policy is denied. Account for inherited descriptors, aliases, delegation,
mounts, and all execution paths that can confer authority. A textual path prefix
alone does not establish filesystem confinement.

## validation: Reject unsupported requests

Validate policy shape, conflicting rights, platform support, and enforcement
prerequisites before guest execution. Unsupported fields or features must fail
explicitly; a missing enforcement mechanism must never silently weaken a policy.
Validation must not assume that arbitrary policy input is benign.

## evolution: Preserve authority under extension

Define policy composition and delegation before implementing them. Extensions
must preserve established guarantees or introduce an explicitly versioned
contract, with migrations and remaining obligations recorded. Avoid freezing a
large policy syntax before the first executable slice needs it.
