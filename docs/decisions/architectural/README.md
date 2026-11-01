# Architectural decisions

| Decision | Subject |
|---|---|
| [§DA-lean-linux](DA-lean-linux.md#da-lean-linux-build-a-lean-replacement-with-linux-as-the-first-backend) | Lean replacement, Bubblewrap reference, Linux first |
| [§DA-m1-filter-profile](DA-m1-filter-profile.md#da-m1-filter-profile-fix-the-first-filter-and-launch-boundary) | Canonical x86-64 M1 filter and explicit source/launch departures |
| [§DA-m2-profile](DA-m2-profile.md#da-m2-profile-fresh-root-helper-and-owned-pid-namespace-for-m2) | Fresh root helper, sealed image and PID-namespace supervisor for M2 |
| [§DA-m3-profile](DA-m3-profile.md#da-m3-profile-frozen-runtime-copied-workspace-and-distinct-run-authority) | Frozen runtime, copied workspace and distinct concurrent-run authority |
| [§DA-m4-effects](DA-m4-effects.md#da-m4-effects-separate-byte-aware-effects-from-compcert-compiler-traces) | Byte-aware native effects and process loss without inheriting compiler trace theorems |
| [§DA-m4-controller](DA-m4-controller.md#da-m4-controller-extend-source-correspondence-through-small-controller-routines) | Small controller source slices with explicit parsing, memory and aliasing contracts |
| [§DA-grund](DA-grund.md#da-grund-trial-pinned-grund-inside-this-repository-only) | Project-local Grund trial |
| [§DA-secondary-backend](DA-secondary-backend.md#da-secondary-backend-consider-sele4n-after-the-first-useful-linux-profile) | Optional seLe4n track after M3 |
