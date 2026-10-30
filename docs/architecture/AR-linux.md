# AR-linux: Connect a Lean launcher to real Linux enforcement

To realize [§FS-launch](../functional-spec/FS-launch.md#fs-launch-establish-containment-before-executing-the-guest) and [§FS-isolation](../functional-spec/FS-isolation.md#fs-isolation-confine-all-supported-guest-effects) on native workloads, Linux mechanisms
enforce restrictions after the Lean launcher has set them up. Bubblewrap supplies
selected reference behaviors under [§FS-compatibility.reference](../functional-spec/FS-compatibility.md#reference-compare-without-overstating-equivalence).

## bindings: Explicit OS contracts

For every binding, document ABI layout, pointer/handle ownership, integer widths,
errors, retries, privilege requirements, and concurrent effects. Keep foreign code
small and separately identifiable. Native guests are not interpreted inside Lean.
A proof of the Lean setup sequence initially relies on contracts for these calls.

## reference: Pinned production reference

Use Bubblewrap v0.13.1 at `362936aea0d5c6e70f7af75d2d44b5a914cb4ba2`.
Begin at [§FS-filter-loading.reference](../functional-spec/FS-filter-loading.md#reference-source-boundary). Maintain a source-to-contract map and
differential tests for the supported subset; neither establishes formal equivalence
to the original C binary. Stricter input validation must be documented.

## platform: Isolated integration profile

The initial upstream Linux reference is 6.18.59. Before runtime integration,
record the exact kernel source/image hash, build configuration, userspace/ABI,
privileges, CPU model, microcode, and relevant firmware/boot assumptions.
Run guest experiments in a disposable VM or explicitly designated test machine.
Do not replace or reconfigure the shared development host's kernel.

The host's installed kernel or Bubblewrap is not automatically this reference.
M0 installs neither. A version label alone is insufficient artifact evidence.

## correspondence: Reduce the Linux assumption

M4 must connect contracts to the relevant pinned Linux code and its transitive
dependencies, together with compiler/runtime/FFI correspondence under
[§FS-assurance.assumptions](../functional-spec/FS-assurance.md#assumptions-initial-assumption-and-obligation-register). Manual code review and conformance tests are useful
evidence but cannot close these proof obligations by themselves. Scope each result
to the actual supported configuration.
