# DA-secondary-backend: Consider seLe4n after the first useful Linux profile

**Status: accepted as a later optional track.** Start a seLe4n backend only after
M3's useful Linux sandbox. Reuse the portable interfaces in [§AR-core](../../architecture/AR-core.md#ar-core-separate-portable-security-contracts-from-platform-mechanisms) for
[§FS-compatibility.matrix](../../functional-spec/FS-compatibility.md#matrix-initial-compatibility-matrix); it is not a prerequisite for the Linux verification path.

## rationale: Test reuse without moving the goal

A second kernel model can exercise policy, state, and proof-interface portability.
It does not discharge Linux assumptions or establish Linux security. M6 can
proceed independently of M4 and M5 after its M3 entry gate.

## obligations: Audit a separate chain

Before adoption, pin and review [seLe4n](https://github.com/hatter6822/seLe4n),
its license, toolchain compatibility, native bindings, and its
[hardware-boundary contracts](https://github.com/hatter6822/seLe4n/blob/main/docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md).
Do not confuse seLe4n with seL4 or import either project's guarantees by name.
Its then-current trusted contracts and proof scope need their own evidence record.
No seLe4n source is vendored or built in M0.
