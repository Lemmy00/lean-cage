# FS-isolation: Confine all supported guest effects

To meet [§GOAL-native-isolation](../goals.md#goal-native-isolation-contain-arbitrary-native-workloads), confinement must hold for arbitrary adversarial
guest execution under the stated platform assumptions and [§FS-policy.authority](FS-policy.md#authority-resources-and-permitted-operations).
The property must quantify over reachable executions, not only sample programs.

## filesystem: Object-level confinement

Specify read, write, creation, deletion, and execution authority for runtime files
and workspaces. Include inherited/open handles, symlinks, hard links, rename races,
mount aliases, procfs, and concurrent changes. A read-only mount is one mechanism;
it does not by itself establish the entire filesystem property.

## process: Memory and process boundaries

Account for address spaces, process discovery/control, credentials, signals,
debugging, shared memory, and fork/exec inheritance. The guest must not gain
authority through another process or by creating a descendant.

## external: Other channels and resources

Specify IPC, devices, networking, and descriptor transfer. Early profiles disable
unsupported channels; later profiles introduce explicit capabilities and proofs.
The first useful workspace profile has no network authority.

## interference: Concurrency and environment

State which interference is possible from other guests and host processes.
Security arguments must cover allowed schedules and races. A trusted operator
who changes the host or policy is outside the untrusted-guest model; ordinary
co-resident workloads and observable interference cannot simply be omitted.
