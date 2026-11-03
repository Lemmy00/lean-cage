# AR-m4-routes: Early Lean and pinned Linux connection attempts

The source results supporting [§FS-assurance.native](../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence) still need the ordinary Lean
connection required by [§REQ-proof-integrity.kernel](../requirements/REQ-proof-integrity.md#kernel-kernel-checked-evidence), and a producer for actual Linux
effects. These experiments advance the feasibility work for `M4-controller`,
`M4-supervisor`, `M4-m3-results` and the artifact obligations. They close none of
the original sixteen entries. Follow `M4-CONTINUE.md` before extending setup.

## lean: Checked semantics route and its current blocker

Inspect the experimental Certora Clight port at commit
`123f7f7767e215aceb4821f0d044336d78103ade`, separately from maintained dependencies.
Build its actual semantics with the project's existing Lean 4.35 toolchain,
inspect the complete type and transitive axioms of `CC.doStep_sound`, export the
actual `CC.Step` closure and attempt its import with the unchanged strict Rocq
profile. Preserve the direct trial and the trial generating `Scheme All` for the
predeclared list. No disabled kernel checking or skipped import errors is allowed.

The necessary next theorem is an explicit state/value/memory/event relation
between that actual Lean `CC.Step` and the pinned Rocq `Clight.step2`, including
function entry, errors, pointers and externals. Importing terms would only make
this statement expressible in Rocq; it would not prove semantic faithfulness or
the ordinary Lean security connection. The port's memory representations,
floating-point implementation, external relations and omitted compiler support
need review. Its ordinary Lean interpreter soundness is a theorem about its own
semantics. Do not apply stock CompCert correctness to that hand port.

The strict import currently fails at nested type `CC.Ty`, in the importer's
recursor handling. Generating the list scheme does not resolve it. The revised
route is a separately reviewed, strictly checked nested-recursor translation,
followed by primitive and full step-relation equivalence; an alternative is a
certificate checker in ordinary Lean for the exact Rocq proof/semantics closure.
Neither route is implemented by this feasibility result. Keep the existing
pure-parser import and its translation-faithfulness obligation separate.

## linux: Pinned reporting-channel source attempt

Use only the existing disposable-VM profile's pinned Linux 6.18.59 source,
archive, configuration and saved `fs/pipe.c` compilation flags. Preprocess the
unchanged configured translation unit into an isolated output directory and
attempt translation with the maintained CompCert frontend. Do not alter the
kernel, native helper, headers, configuration or shared host. Record compiler,
input, generated-byte and diagnostic identities. This is source processing,
with no kernel or guest workload execution.

The actual attempt stops at the Linux header's `__int128` declaration. Removing
that type or replacing kernel concurrency with sequential behavior would change
the assigned semantics. The replacement route must give a checked semantics for
the required GNU C, atomic, memory and architecture operations, or prove a
source refinement from those operations to an explicit concurrent kernel model.

The required reporting producer relates actual descriptor ownership and pipe
contents to `IO.io_return`, including libc/TLS error conversion, short transfer,
EINTR/EOF, loss, inherited aliases and interference. The read path at
`anon_pipe_read` additionally requires a proof about partial user-copy faults:
the source can reach `-EFAULT` after a short copy, whereas the current local
failure constructor changes only errno. If an earlier buffer already contributed
to the return count, a later partial copy can instead leave additional bytes
beyond that positive count, while `read_returns` writes exactly the returned
prefix. Both branches need an explicit memory relation. This is an unresolved producer
obligation, not a demonstrated counterexample under the owned-buffer deployment
premises. Establish the relevant page-fault/memory guarantees or explicitly
version the effect contract and revalidate its consumers.

## evidence: Replay and claim boundary

Maintain exact attempt inputs, full ordinary Lean audit output and both failed
import diagnostics. Retain the configured kernel preprocessing and translation
diagnostics. A normal gate checks reviewed records; collecting a report never
refreshes them. Unexpected success or a different failure requires review.
Preserve upstream licenses and distinguish this experimental inspection pin
from the maintained compiler, Lean, runtime and VM pins.

These are reproducible failed connection attempts and a revised research route.
They prove neither imported-semantics equivalence nor a Linux effect producer,
compiler composition or a sandbox property. Do not extend dependent source
proofs while describing those central missing connections as routine paperwork.

## reporting: Continue through the original reporting closure chain

The active target is the original `M4-m3-results` entry under
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport), including transport provenance, output bounds,
authorized export and publication failure. The accepted source proofs are inputs
to this target. Their count and replay status are not its closure criterion.

### reporting.chain: Required producer-to-consumer chain

Connect actual helper/controller execution and owned pipe/output/filesystem
objects to the M3 observations consumed by `decodeResult`, `observe` and report
publication. Preserve arbitrary permitted interference, short transfers, errors,
partial user copies, loss, unknown entry/cleanup and failed publication. Include
the actual runtime/ABI and identified executable chain. All connecting premises
must have explicit producers; a theorem assuming the desired effect or reporting
property does not discharge that edge.

Track progress by the following connecting edges, retaining their dependencies
on the other original obligations:

1. An ordinary Lean semantics/security theorem connected to the exact source
   transition system and original Lean computations.
2. Actual pinned Linux reporting effects, descriptors, concurrency and memory
   related to that source system, including the partial-copy fault branches.
3. Helper/controller ordering and observation composition through capture,
   export, report construction and failed publication.
4. The compiler/runtime/loader realization needed for those identified sources
   and deployment artifacts; preserve the separate original artifact obligations.

### reporting.bridge: Repair the shared semantics bridge

Start with the actual failed `CC.Step` import recorded by
[§AR-m4-routes.lean](AR-m4-routes.md#lean-checked-semantics-route-and-its-current-blocker). The imported `CC.Ty` contains recursion through a list;
its exported Lean eliminators include the secondary list motive and its cases.
Generate and kernel-check the corresponding dependent recursors, their complete
types and constructor reduction equations. A weak induction principle for only
the outer type is insufficient. Unsupported nested or mutual forms must fail
explicitly, and every generated declaration enters the checked inventory.

Develop the importer repair in a separate project-local tool copy. Preserve the
accepted importer, its strict patch, snapshots and dependency pins. Keep all
guardedness, positivity, universes, conversion and elimination checks enabled;
introduce no axioms or proof placeholders. Test the actual exported closure and
compiled counterexamples as well as the smallest nested-type reproducer.

The producer sought after import is a checked relation between the actual Lean
semantics and pinned Rocq `Clight.step2`, with state, value, memory, ABI and event
representations. Constructor reduction checks support that connection but do not
replace its semantic proof. Continue along the chain after each prerequisite is
discharged instead of treating a failed attempt as a completed obligation.

### reporting.instances: Preserve the actual requested representations

Use the exported `UInt32`, `Char` and supporting definitions from the inspected
Lean version. Do not bind a newer field projection to an older primitive with a
different representation. Demand individual universe instances of definitions;
registering their metadata does not assert that every instance has been translated.
An unsupported instance requested by the target must fail.

Reduce `autoParam` and `optParam` type wrappers only after checking that the
exported transparent body is exactly the two-argument projection of its first
argument. This is source delta/beta reduction. Check the equations in the original
Lean toolchain as well. Retain all actual target computations and proof premises;
this reduction supplies no source-semantics or compiler correctness theorem.

The strict accessibility test must continue to reject elimination from recursive
strict propositions into computational types. An instance producing a strict
proposition may use its kernel-checked small eliminator. Never enable unchecked
elimination to bypass an unsupported computational instance.

For noncomputational proof constants, a replacement Rocq proof may establish
exactly the exported strict-proposition type. Kernel-check that entire type,
including all parameters and hypotheses, and the replacement proof. Reject
computational result sorts and unsupported universe instances. Proof irrelevance
permits this replacement; it supplies neither an arbitrary proposition nor a
replacement implementation. Audit the replacement's foundations and preserve the
original Lean statement and evidence. Any numeric representation adapter also
requires a checked value-equivalence proof.

### reporting.types: Relate the actual type representations

Use the imported actual `CC.Ty` and the pinned CompCert `Ctypes.type` to establish
a total representation bijection. Cover every type constructor and both nested
function-argument lists, positive identifiers, unbounded integer array lengths,
optional alignment exponents, volatile flags and all calling-convention fields.
Prove both round trips with no narrowing or extra validity premise. Use the
checked exported nested recursor where its dependent list hypothesis is needed.

This type relation is a producer for the state/expression/ABI relation in
[§AR-m4-routes.reporting.bridge](AR-m4-routes.md#reportingbridge-repair-the-shared-semantics-bridge). It does not establish expression, memory, transition or compiler
correspondence. Those connecting edges remain required by
[§AR-m4-routes.reporting.chain](AR-m4-routes.md#reportingchain-required-producer-to-consumer-chain).

### reporting.closure: Original ledger acceptance

Close `M4-m3-results` only after the complete chain proves the original advertised
property with ordinary Lean theorem terms under
[§REQ-proof-integrity.kernel](../requirements/REQ-proof-integrity.md#kernel-kernel-checked-evidence). Audit full statements, foundations, deployment inputs and
all transitive connecting assumptions; provide nonvacuity and independent replay.
Update the original ledger with that closure evidence. Preserve the original
meaning of its key, and distinguish any still-open shared artifact dependency.
Hardware-channel confidentiality remains M5.
