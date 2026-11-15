# DA-host-delivery: Deliver the host boundary in two parts, engine first

**Status: planning revision, 2026-11-15, made at the user's request for a
reduced M5.2 scope.** It sequences
[§AR-host-boundary.acceptance](../../architecture/AR-host-boundary.md#acceptance-integrate-before-advertising-the-guarantee) for [§FS-host-boundary.acceptance](../../functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation). The complete
host contract in [§AR-application-verification.host](../../architecture/AR-application-verification.md#host-safe-host-boundary-for-arbitrary-vm-output) remains the destination.

## decision: Split the host delivery at the engine process

Two programs implement the host boundary. The Lean engine `leancage-host` makes
every host security decision and performs every host filesystem and VM effect.
The C Python extension `linux/host_python.c`, called the gateway, passes the
caller's arguments to that engine and turns its typed response into Python
objects.

- **M5.2 is the host engine guarantee.** It is accepted under
  [§AR-host-boundary.acceptance.engine](../../architecture/AR-host-boundary.md#acceptanceengine-m52-closes-on-the-engine-guarantee-and-both-callers): the engine theorem for whole executions,
  both public callers running through the engine by default, and the earlier
  Python host implementation removed from the public path.
- **The gateway proof is its own delivery, M5.2b**, accepted under
  [§AR-host-boundary.acceptance.gateway](../../architecture/AR-host-boundary.md#acceptancegateway-m52b-proves-the-native-caller-and-supplies-the-engine-premises). It follows M5.4 and precedes M5.5.
- **The proof that a stored result was written by this installation's
  publisher moves to M5.5**, which already owns retrieval provenance.

M5.3 and M5.4 are unchanged. M5.5 additionally consumes M5.2b and proves
publisher authentication. [§FS-linux-product.proofs.application](../../functional-spec/FS-linux-product.md#proofsapplication-the-complete-application-guarantee) still requires
every part. None of the moved work becomes a permanent assumption.

## reason: The engine result is usable alone and the gateway proof did not converge

At the checkpoint of 2026-11-10 the engine program has a kernel-checked
functional theorem, `CallerProofs.actual_application_complete`, and filesystem
custody results for individual operations. Its whole-execution custody theorem
is unfinished. The gateway proof holds most of the remaining work. It depends
on hand-written contracts for the CPython and libc operations. One of them was
proved contradictory (`assurance/host-reference-ownership-amendment.json`), and
no model yet satisfies those contracts together. Two successive checkpoints
recorded the same eight open ownership items, and the open response items went
from five to four, while the checked supporting interfaces grew from 43 to 60.
The public callers still use the earlier Python host implementation, so no
caller receives the engine's checked behavior.

[§FS-linux-product.trust](../../functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product) already defines the state the gateway enters: an
enumerated native adapter, tested and listed as trusted, until its
correspondence proof is supplied. The project rule in `AGENTS.md` divides a
large assignment at a functional interface whose result can be integrated and
used; the engine process interface is such an interface.

## engine: What M5.2 proves and which premises it names

The engine guarantee covers every request packet, every VM byte stream and the
permitted filesystem interference, including failed and lost operations. It
keeps every claim of [§FS-host-boundary](../../functional-spec/FS-host-boundary.md#fs-host-boundary-preserve-host-authority-and-bounds-for-arbitrary-vm-bytes) about snapshots, transport, artifact
validation, publication and the retrieval checks. Ownership of this request's
private directories is still derived from the individual Linux operation
contracts and the actual creation history. It does not become an assumption.

The engine theorem has these named premises and no others:

| Premise | Content | Producer |
|---|---|---|
| Engine start | Descriptors 0, 1 and 3 are the request, response and cancellation endpoints, held only by the calling process; the argument vector, environment and engine image are the fixed identified ones | M5.2b |
| Calling process | Code in the calling process follows host-code profile 1 of [§FS-host-boundary.ownership](../../functional-spec/FS-host-boundary.md#ownership-derive-fresh-objects-and-retain-their-identity); the gateway's own C code runs in that process | External caller requirement; the gateway's part by M5.2b |
| Child processes | The policy validator and the VM process have their recorded individual process contracts; reaping is observed, never assumed | Existing contracts; owned lifetime by M5.4 |
| Platform | The individual Linux, runtime and cryptographic operation contracts of [§AR-host-boundary.primitives](../../architecture/AR-host-boundary.md#primitives-enumerate-the-linux-and-runtime-effects) | [§FS-linux-product.trust](../../functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product) |

The existing `NativeAuthorityProfile` and `NativeLookupProfile` parameters
already express the calling-process premise for trusted parents. The open items
`native-handoff-coupling` and `native-callback-operation-coverage` in
`assurance/host-ownership-status.json` become the engine-start and
calling-process premises.

## gateway: What M5.2b proves

M5.2b proves the caller part of [§FS-host-boundary.acceptance](../../functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation) for the unchanged
gateway behavior in [§FS-host-boundary.caller](../../functional-spec/FS-host-boundary.md#caller-preserve-the-public-request-and-result-interfaces): argument extraction, request
construction, the fixed spawn arguments and descriptors, the exchange loop,
response parsing, `Outcome` construction and observation, initialization and
reference ownership. It supplies the engine-start premise and the gateway's
part of the calling-process premise. The checked gateway components and proof
sources stay in the repository as its inputs.

Before M5.2b is accepted, no claim may state that the Python library or the
CLI wrapper passes inputs or results unchanged, or that the gateway's C code is
memory-safe. The claim record lists the gateway as a tested, unproved native
adapter with its named functions.

## publication: Publisher authentication is proved with retrieval provenance

The engine keeps the marker and HMAC behavior of [§FS-host-boundary.publication](../../functional-spec/FS-host-boundary.md#publication-preserve-observations-through-storage-and-retrieval).
M5.2 proves that retrieval performs its binding, hierarchy, bound, digest and
marker checks before it returns stored content. M5.2 does not prove that a
stored result accepted by those checks was written by this installation's
publisher. That proof needs key-byte nonexposure over the key's whole lifetime
and the stated unforgeability assumption. It moves to M5.5.

## consequences: State the reduced claim and prevent the same stall

- After M5.2, the advertised host property names the engine and the premises
  above. It does not describe the Python library as verified.
- The default callers then run the unproved gateway. Its recorded
  signal-target defect is repaired before that change, and the gateway tests
  belong to M5.2's acceptance run.
- Each delivery starts from its written final statement and a model that
  satisfies its contracts. Progress is the number of closing statements
  proved. [§RM-roadmap.m5.next](../../roadmap.md#m5next-current-assignment) sets the effort limit after which work without a
  newly proved closing statement ends in a report to the user.
- Records for the gateway proof keep their scope. A gateway source change
  needed by M5.2 may leave some of them unreplayed; those are listed as
  excluded. They are not deleted and their expectations are not refreshed.
