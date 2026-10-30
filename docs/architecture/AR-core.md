# AR-core: Separate portable security contracts from platform mechanisms

To realize [§FS-policy](../functional-spec/FS-policy.md#fs-policy-grant-only-explicit-supported-authority), [§FS-isolation](../functional-spec/FS-isolation.md#fs-isolation-confine-all-supported-guest-effects), and [§FS-observations](../functional-spec/FS-observations.md#fs-observations-state-exactly-what-an-attacker-may-observe), the planned core
contains policy, authority, sandbox state, observable events, and execution traces.
The M0 library currently imports Velvet only; these modules are not implemented.

## state: Extensible state and effects

Define explicit states and transitions for launch and guest execution. Backend
operations describe effects, results, failures, and allowed concurrent interference.
Use abstract resource identities and handles where concrete paths would conceal
aliasing. Keep policy independent of CLI serialization and backend-specific flags.

## adversary: Quantify over hostile execution

Permit arbitrary guest steps allowed by the concrete environment. State invariants
must survive those steps, fork/exec, signals, and races; proving only the launcher's
own calls is insufficient for full confinement. Each backend must establish that
its concrete executions refine this model.

## observations: Keep observation boundaries explicit

Define observation functions and authorized disclosures from the beginning.
Layer logical and hardware-aware observations without treating a functional trace
projection as proof of timing confidentiality. Cross-backend reuse requires
preserving the actual claimed observation property.

## interfaces: Planned module boundaries

Grow the library as needed into policy/state, launch/filter, backend contracts,
Linux bindings, proofs, and assurance reporting. Implement the future library and
CLI of [§FS-compatibility.interface](../functional-spec/FS-compatibility.md#interface-future-commands) only when their first behavior is specified;
do not create commands that imply unsupported containment.
