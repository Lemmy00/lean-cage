# FS-filter-loading: Prove a small real launch boundary first

The first executable slice serves [§GOAL-end-to-end](../goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact) and [§FS-launch.order](FS-launch.md#order-explicit-lifecycle). It covers
loading a supported syscall-filter representation and installing it before guest
execution, using pinned Bubblewrap behavior as its starting point.

## input: Bytes, bounds, and ABI

Specify byte decoding, instruction layout, byte order, alignment, machine-width
arithmetic, length bounds, narrowing conversions, and the selected architecture
and syscall ABI. Reject malformed, oversized, empty if unsupported, or mismatched
inputs before execution. Do not replace machine integers with unbounded naturals
without proving the conversion obligations. A supported policy-to-filter path
must check the architecture and fail closed on an unsupported ABI.

## installation: Success and failure traces

Prove that execution is reachable only after every required restriction and
filter installation succeeds. Cover installation failure and interrupted setup.
For a supported ordered filter list, specify its composition/order before adding
the multi-filter extension; a single-filter subset is sufficient initially.

## claim: Limited first theorem

Separate decoding/installation correctness from what the installed filter permits.
A well-formed arbitrary filter can allow every syscall. A demonstration must use
an explicitly restrictive policy/filter and show an allowed action succeeding and
a denied action being blocked. At M1, actual kernel enforcement is an assumption;
the demo and the abstract launch theorem do not prove Linux or full isolation.

## reference: Source boundary

Use Bubblewrap v0.13.1, commit `362936aea0d5c6e70f7af75d2d44b5a914cb4ba2`:
[`seccomp_program_new` and `seccomp_programs_apply`](https://github.com/containers/bubblewrap/blob/362936aea0d5c6e70f7af75d2d44b5a914cb4ba2/bubblewrap.c#L245),
plus the no-new-privileges setup and final filter-to-exec path in that file.
Track error exits, the length conversion to `sock_fprog.len`, and operations
between filter installation and `execvp`. This is a source map, not an equivalence
proof or authorization to copy code without preserving its license.
