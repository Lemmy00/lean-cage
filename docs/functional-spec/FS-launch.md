# FS-launch: Establish containment before executing the guest

To meet [§GOAL-native-isolation](../goals.md#goal-native-isolation-contain-arbitrary-native-workloads) and [§FS-policy.validation](FS-policy.md#validation-reject-unsupported-requests), the launcher must finish
all required isolation and restriction steps before any untrusted guest code runs.

## order: Explicit lifecycle

Specify validation, creation of the isolated environment, privilege reduction,
inherited-resource handling, enforcement installation, and guest execution as
state transitions. State precisely which setup operations may run in the parent
or child. Only a state satisfying the selected profile's launch invariant may
transition to guest execution.

## failure: Fail closed

Validation or setup failure must prevent guest execution and report a distinguishable
error. A failed syscall, partial operation, retry, signal, or cancellation must not
open an alternate execution path. Proving that the success path is safe does not
discharge failure-path obligations.

## lifetime: Descendants and teardown

Define the containment lifetime, ownership of children and descendants, exit status,
cancellation, and cleanup. Descendants must retain restrictions across fork and
exec. Cleanup must not remove unrelated resources. Later milestones must cover
concurrent interference and failures during teardown, not just sequential setup.
