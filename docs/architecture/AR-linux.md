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

[§AR-filter-slice.source](AR-filter-slice.md#source-pinned-bubblewrap-path) maps the first filter/exec segment and records source
hashes, ABI definitions, ownership and concurrency boundaries, and intentional
departures. M1's original native binding and call map are in [§AR-m1-launch.binding](AR-m1-launch.md#binding-small-native-boundary);
the Bubblewrap map remains reference evidence, not source equivalence.

## platform: Isolated integration profile

The M1 integration reference is Linux 6.18.59, commit
`1253a6aa5d104312bf0992afacc15220ae35bdf9`, built from the SHA-256-pinned upstream
archive in `tests/vm/bootstrap-pins.json`. `tests/vm/linux-6.18.59.config` is the
resolved build configuration; `kernel.fragment` explains the principal choices.
`assurance/m1-vm-evidence.json` records exact kernel/image/configuration,
initramfs/userspace, QEMU/TCG, firmware, compiler/runtime, commands, and virtual
CPU/microcode identities. [§FS-assurance.demo](../functional-spec/FS-assurance.md#demo-m14-isolated-linux-test-record) records the result and its limits.
Run guest experiments in a disposable VM or explicitly designated test machine.
Do not replace or reconfigure the shared development host's kernel.

The VM uses one emulated vCPU, 2048 MiB RAM, no NIC, persistent disk, or host
mount, root PID 1, and an unprivileged UID/GID 65534 launcher/guest. Its virtual
microcode value is emulator metadata, not a measurement of physical microcode.
There is no hardware leakage claim. The host's installed kernel or Bubblewrap
is not this reference; no host filter or kernel replacement is part of this work.

## correspondence: Reduce the Linux assumption

M4 must connect contracts to the relevant pinned Linux code and its transitive
dependencies, together with compiler/runtime/FFI correspondence under
[§FS-assurance.assumptions](../functional-spec/FS-assurance.md#assumptions-initial-assumption-and-obligation-register). Manual code review and conformance tests are useful
evidence but cannot close these proof obligations by themselves. Scope each result
to the actual supported configuration.
