# DA-secondary-backend: Consider seLe4n after the first useful Linux profile

**Status: accepted as a separate planned backend track.** M3's useful Linux
sandbox satisfies its entry gate. Reuse the portable interfaces in [§AR-core](../../architecture/AR-core.md#ar-core-separate-portable-security-contracts-from-platform-mechanisms) for
[§FS-compatibility.matrix](../../functional-spec/FS-compatibility.md#matrix-initial-compatibility-matrix); it is not a prerequisite for the Linux verification path.
The current delivery assignment is [§RM-roadmap.m6.sele4n](../../roadmap.md#m6sele4n-a-sele4n-backend-using-the-same-portable-contracts). No backend implementation
or dependency adoption is implied by this planning decision.

## rationale: Test reuse without moving the goal

A second kernel model can exercise policy, state, and proof-interface portability.
It does not discharge Linux assumptions or establish Linux security. M6 can
proceed independently of M4 and M5 after its M3 entry gate.

## delivery: Connect a real execution profile to the reusable core

Keep policy, authority, lifecycle observations and typed results shared with the
Linux product. Implement capability-based realization behind those interfaces.
The first profile supplies one allowed native workload, a denied authority use,
bounded returned output and termination/cleanup, with a checked refinement for
that subset. It has its own supported ABI/runtime and identified kernel bundle.
An executable model alone does not meet the runtime acceptance contract.

## obligations: Audit a separate chain

Before adoption, pin and review [seLe4n](https://github.com/hatter6822/seLe4n),
its license, toolchain compatibility, native bindings, and its
[hardware-boundary contracts](https://github.com/hatter6822/seLe4n/blob/main/docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md).
Do not confuse seLe4n with seL4 or import either project's guarantees by name.
Its then-current trusted contracts and proof scope need their own evidence record.
Resolve the actual boot/userspace path and compatible compiler/runtime before
expanding the adapter. Keep its toolchain isolated if the pins differ from the
Linux product. Distribution must follow upstream licensing. No seLe4n dependency
is added by the current Linux product assignment.
