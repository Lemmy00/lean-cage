# DA-m2-profile: Fresh root helper and owned PID namespace for M2

Implement [§FS-lifecycle.profile](../../functional-spec/FS-lifecycle.md#profile-supported-entry-and-privilege-boundary) and [§FS-lifecycle.supervision](../../functional-spec/FS-lifecycle.md#supervision-stable-ownership-and-typed-results) using
[§AR-lifecycle.design](../../architecture/AR-lifecycle.md#design-executable-boundary-reviewed-before-native-implementation) and [§AR-lifecycle.vm](../../architecture/AR-lifecycle.md#vm-separate-capable-disposable-profile). Accept one VM-only root-helper profile,
with user namespaces disabled and five explicitly created namespaces. The helper
is an ordinary static executable invoked by a trusted root Lean controller; it is
not installed setuid and has no shared-host deployment path.

## rationale: Stable identity and honest executable boundary

A fresh exec avoids running Lean runtime/allocator work in a forked child. A fixed
validated plan makes the native order reviewable without pretending the C program
is the proved Lean transition function. A sealed executable handle closes M1's
path relookup gap. An owned PID namespace handles double-fork/session escape and
gives teardown a precise scope. A trusted ptrace exec event distinguishes real
image replacement from empty/failed reporting and permits guest exit 125.

## limits: Explicit costs and rejected alternatives

Root administration and native/Linux correspondence remain assumptions. This
profile does not address M3 filesystem authority or dynamic runtimes. Unprivileged
user-namespace launch, existing-filter composition, arbitrary stdio handles and
other architectures fail closed. Keeping M2 in a dependent Lake package preserves
the original M1 build and evidence instead of changing its contracts for convenience.
The supported signature/plan is versioned; extensions require new reviewed contracts.
