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
