# AR-core: Separate portable security contracts from platform mechanisms

To realize [§FS-policy](../functional-spec/FS-policy.md#fs-policy-grant-only-explicit-supported-authority), [§FS-isolation](../functional-spec/FS-isolation.md#fs-isolation-confine-all-supported-guest-effects), and [§FS-observations](../functional-spec/FS-observations.md#fs-observations-state-exactly-what-an-attacker-may-observe), the core
contains policy, authority, sandbox state, observable events, and execution traces.
M1 supplies the first launch vocabulary under [§AR-m1-launch.model](AR-m1-launch.md#model-total-transitions-and-trace-evidence).
M2 extends lifecycle/ownership and M3 implements bounded policy, authority,
process/resource and functional-observation interfaces under [§AR-workspace.interfaces](AR-workspace.md#interfaces-portable-objects-state-and-effect-results).
Their native/Linux refinement and hardware-aware observation obligations remain
open. [§AR-product.execution](AR-product.md#execution-current-path-from-policy-to-workload-and-report) identifies the single current runtime path.

## state: Extensible state and effects

Define explicit states and transitions for launch and guest execution. Backend
operations describe effects, results, failures, and allowed concurrent interference.
Use abstract resource identities and handles where concrete paths would conceal
aliasing. Keep policy independent of CLI serialization and backend-specific flags.

The first vocabulary is `LeanCage/Launch/Contract.lean`: stages, effect requests,
OS-call labels, terminal failure reasons, and public events. It imports no Linux
definitions. `LeanCage/Launch/Model.lean` adds a total stage/event transition and
finite replay; `LeanCage/Proofs/Launch.lean` proves receipt and exact-order
invariants, failure absorption, replay/reachability equivalence, and nonvacuity.
The validation verdict is connected to the actual decoder in
`LeanCage/Proofs/LaunchInput.lean`; OS-effect honesty remains an assumption.
Its M1 scope is [§FS-filter-loading.installation.states](../functional-spec/FS-filter-loading.md#installationstates-launch-states-and-permitted-effects). The dependent M2/M3 packages
add their own lifecycle and hostile-guest models; the composition and remaining
effect contracts are recorded in [§FS-assurance.workspace](../functional-spec/FS-assurance.md#workspace-m3-workspace-model-and-vm-evidence).

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

## interfaces: Module boundaries and current entry point

The current executable entry is `m3/Main.lean`; its `LeanCageM3.API` library connects
the versioned policy/results to the native helper. [§AR-product.execution](AR-product.md#execution-current-path-from-policy-to-workload-and-report) maps
that path to Linux enforcement, guest execution and stored artifacts. Keep the
policy/state, launch/filter, backend contracts, Linux bindings, proofs and
assurance boundaries reusable while maintaining that runnable path. Extensions
to [§FS-compatibility.interface](../functional-spec/FS-compatibility.md#interface-versioned-commands) must retain an explicit supported profile and renewed evidence.
