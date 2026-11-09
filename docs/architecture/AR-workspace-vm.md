# AR-workspace-vm: Own the caller request, disposable VM and returned artifacts

Implement [§FS-linux-product.operation](../functional-spec/FS-linux-product.md#operation-run-a-callers-workload-through-one-supported-interface), [§FS-linux-product.transport](../functional-spec/FS-linux-product.md#transport-carry-requests-and-results-across-the-vm-boundary) and
[§FS-linux-product.trust](../functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product) using the existing offline-workspace policy, controller,
helper and pinned VM. The host library and CLI share one implementation.

## request: Freeze bounded caller inputs before boot

The host accepts the existing version-1 JSON policy (at most 65536 bytes) and
validates its exact bytes with the shipped Lean controller. Optional workspace
and stdin paths are copied through descriptor-relative, no-follow reads. Only
directories and regular files are supported; reject links, special files, unsafe
UTF-8 names, excessive depth, entries or bytes. Copy before boot, hash the copied
bytes, and require their hashes to match any input identities already supplied
by the policy. The `--workspace` and `--stdin` options bind previously null input
identities to these frozen snapshots. The host constructs the existing LCTREE1
format and content-addressed blobs. Inputs are capped by the policy,
the 4 MiB tree format, 64 MiB stdin and 256 MiB workspace bounds.

Each invocation has a random 128-bit request identity and the SHA-256 identity
of the bundle manifest. The trusted host creates a fresh private run directory
and initramfs overlay containing the policy, request identity and snapshots.
There is one request per VM; no host filesystem, network device or persistent
disk is exposed. No supplied argument is evaluated as a host command.

## channel: Separate trusted framing from guest output

The recorded kernel supports a second 8250 UART. COM1 carries boot diagnostics;
COM2 is a private Unix-socket-backed, raw, bidirectional control channel owned by
the host runner and trusted VM init. Guest `/dev` does not expose either UART.
The controller's private helper pipe and bounded captures remain unchanged.

The result starts with eight bytes `LCVM1\0\0\0`, the 32 ASCII hex request ID,
and the 64 ASCII hex bundle ID. Records have a 16-byte little-endian header:
32-bit tag, 32-bit reserved zero, 64-bit payload length. Tags are controller JSON
(1), retrieved stored report JSON (2), stdout (3), stderr (4), export manifest
(5), content-addressed blob (6), and terminal status (7). A blob contains its
64 ASCII hex digest followed by file bytes. Terminal status is four unsigned
32-bit values: controller exit, report-retrieval exit, transport error, and
independently observed inner-scope extinction. Exactly one terminal record and
EOF are required. Duplicates, unknown tags, wrong identity, reserved bits,
truncation, trailing data, and exceeded per-record/aggregate limits fail closed.

Reports are bounded to 65536 bytes each; captures to their policy caps; export
manifest to 16 MiB; export blobs to the workspace cap and inode count. Hash and
parse the manifest, reject unsafe/duplicate/conflicting names, and verify every
referenced blob and the report's export digest before publishing files. Return
files only in a fresh host-owned directory, through no-follow relative writes.
The host records the original VM JSON separately from the envelope binding it
to the request, bundle and locally returned artifacts. Boot text has no authority.

## lifetime: Cancellation, loss and publication

The host owns the QEMU process group and socket. The init process owns its
controller and all in-VM processes. A single `C` byte requests cancellation.
Init finds the controller's direct helper through bounded `/proc` status/executable
checks (the pinned kernel omits `CONFIG_PROC_CHILDREN`), opens a pidfd, and waits
until its SIGTERM handler is armed before signaling it. Early cancellation is
remembered. Cancellation remains a request until the helper reports its observed
outcome and cleanup; an exit/cancel race may report the observed exit.

Host cancellation has a bounded grace interval, then terminates and reaps the
owned VM process group. Host timeout, malformed/lost channel or VM death produces
an incomplete result. Successfully reaping QEMU establishes VM teardown only;
it does not establish observed guest entry or helper cleanup. Preserve an already
received valid report when later transport or host storage fails. An incomplete
transport never supplies complete captures/exports. Public storage uses a private
staging directory and atomic rename; storage failure returns the known result
and an explicit publication error. Never replace another run's directory.

## bundle: Build and identify the components actually executed

One root build stages controller, static native helper, static VM init, filter,
runtime initramfs, kernel/configuration, local QEMU/firmware and its dependency
closure. The manifest binds these files, tool versions, pinned runtime identity,
source identities, proof bindings and trusted adapters. Validate those identities
before use. Development proof tools are excluded from the execution bundle.
The existing platform assumptions apply; this transport and the native helper
remain enumerated tested application adapters pending complete source proofs.

## migration: Preserve proof identities while moving maintained components

The migration baseline is commit `d44c961`. Canonical maintained homes are
`lifecycle/` (portable lifecycle), `workspace/` (policy, authority, resources,
reporting and controller), `linux/` (native workspace adapter),
`profiles/offline-workspace/`, `python/leancage/` (host library/CLI), and
`verification/` (current reporting/compiler proofs). The root entry points are
`scripts/build.sh` and `leancage`. Existing module/declaration names and private
version-1 ABI paths are compatibility interfaces: changing them would invalidate
otherwise unchanged theorem terms and source/compiler receipts.

`m2` and `m3` are compatibility symlinks to the corresponding maintained Lake
packages; `native/leancage_m3.c` and its three headers point to `linux/`;
`profiles/m3` points to the supported profile. Runtime/ELF script compatibility
names point to responsibility-named scripts. There are no parallel implementation
copies. Historical milestone test harnesses and proof snapshots stay in place.
When the maintained helper changes, `assurance/workspace-baseline.json.gz`
preserves the predecessor's actual source bytes and scoped receipts; a historical
path in that archive does not identify the current helper through its alias.
The separate sealed `assurance/product-cache-baseline.json.gz` retains the exact
API and Main Lean artifacts named by the accepted reporting/compiler record at
`d44c961`. The migration checker validates their bytes against that record and
keeps its original cache fingerprints; current rebuilt artifacts are recorded
separately. This preserves the workspace predecessor archive and its existing
VM bindings unchanged.
The metadata migration check can run before any generated proof cache exists.
It freezes every original artifact/SDK digest in the manifest and validates the
sealed historical cache bytes; recorded current-cache hashes are past local
observations. Actual artifact availability/content belongs to the corresponding
proof gate, which still rebuilds or checks those artifacts. Maintained sources,
approved operational amendments and original theorem/axiom/scope payloads remain
checked. CI fetches the accepted Git history needed to validate those preimages.
The migration record checks every alias against its canonical target and records
the original revision. Preserve theorem statements and axiom sets exactly;
amend only reviewed operational-document/evidence fingerprints when needed.
