# FS-entry: Value-carrying, fail-closed guest admission

Refine [§FS-linux-product.proofs.entry](FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry) for the maintained offline workspace.
This contract is an implementation target. Delivery includes the caller and
adapter proofs, not only a standalone setup model.

## inputs: Prepared values and local handle validation

Admission receives the leased 32-bit UID/GID, prepared root object/path, owned
namespaces and resource scope, the bounded workload argv, and four owned handle
slots. The stdin, stdout, stderr and failure slots must be distinct, at least
four, and fit a signed 32-bit descriptor. Their objects are respectively the
frozen input, capture writers and private setup-failure writer. Preparation owns
their classification; admission checks the numeric alias restrictions itself.
Argument strings are nonempty, NUL-free UTF-8 within the existing policy bounds.
The first executable remains `/bin/sh` or `/usr/local/bin/python3`.

The private worker handoff carries mode, UID, root, the four descriptor numbers,
the selected test mode and workload argv. Numeric fields use canonical ASCII
decimals: no sign, whitespace, leading zeroes, overflow or narrowing loss.
This internal ABI does not replace the public policy format. The production
native handoff and entry executable both reject non-normal selectors. Fault
injection uses a separate test executable and an explicit native test build.
For normal inputs the two Lean entry builds execute the same definition.

## control: Primitive sequencing and failure

The executing definition must issue concrete operations and inspect their actual
returns. A failed or unexpected setup return cannot reach any later setup
operation or workload exec. Reporting failure, partial writes, asynchronous death
and loss cannot reopen setup. Safety holds for finite execution prefixes;
termination requires primitive progress and scheduling assumptions separately.

Validate PID-valued and mode-valued returns against their actual ranges; neither
zero from a PID-returning operation nor an out-of-range mode is successful setup.

The allowed entry has the requested root and `/workspace` cwd; standard handles
refer to the supplied objects; only the private close-on-exec failure writer may
remain before exec. Signal dispositions/mask, IDs, groups, capability sets,
securebits, dumpability, no-new-privileges and exact filter satisfy
[§FS-linux-product.proofs.entry](FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry). The workload argv and fixed environment are the
values supplied to the successful image-replacement operation.

## check: Preflight never executes a workload

Preflight exercises the same supported setup restrictions without a workload
exec. Its trusted success record is distinct from observed workload entry. Both
preflight and run fail closed; a lost record remains unknown at the receiver.

## provenance: A return value does not prove the requested effect occurred

An inherited seccomp filter can synthesize a successful return without executing
the requested operation. Model that execution as well as genuine kernel returns.
Do not infer credential changes, filter installation or absence of inherited
filters from a raw success status without establishing its provenance. The real
caller must supply the supported clean process lineage, ownership and observation
producers. A body theorem conditional on those producers is not the complete
entry guarantee in [§FS-linux-product.proofs.entry](FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry).

## runtime: Dedicated entry runtime profile

No Lean runtime state may be inherited across a fork into effectful Lean code.
A fresh entry image may use the pinned runtime only with an explicitly identified
startup profile that creates no additional thread. It cannot call task, process
or event-loop APIs. Reset signal state after initialization. Bound argument and
filter memory before confinement, retain it through the corresponding syscall,
and account for allocation failure and unexpected runtime termination as loss.
Runtime/compiler behavior stays in [§FS-linux-product.trust](FS-linux-product.md#trust-platform-assumptions-for-the-initial-product); a runtime
configuration is never evidence for an application control theorem.
