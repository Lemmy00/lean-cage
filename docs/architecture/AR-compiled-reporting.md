# AR-compiled-reporting: Carry reporting observations across verified compilation

This connection serves [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and preserves the claim boundaries
of [§FS-assurance.native](../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence). The original `M4-m3-results`, `M4-artifacts` and
`M4-m3-artifacts` entries remain its delivery targets. [§AR-reporting.proof](AR-reporting.md#proof-check-the-interface-in-both-proof-environments) supplies
the existing source and ordinary Lean decoder argument.

## connection: Carry the reporting argument across verified compilation

Connect the current helper's descriptor-1 `send_frame` source call to identified assembly in
the compiler's transition system. Inputs are the owned source call, a matched
assembly call state and primitive runtime effects. Outputs are the emitted-byte
prefix for every finite assembly execution and the existing decoder result on
successful return. `CompilerCertificate.current_assembly_reporting` consumes
the concrete compilation equation, `sender_all_prefixes` and
`SourceConnection.source_sender_decoder`; the latter consumes the ordinary Lean
publication proof. The integration command is `./scripts/check_reporting_compiler.sh`.

The source proof uses Clight's temporary-parameter semantics (`step2`). Start
the verified backend at `Cshmgenproof.transl_program_correct`; applying
`Compiler.transf_c_program_correct` directly to that source is a type and
semantics mismatch. Compose the pinned compiler's actual remaining pass proofs.
Retain the pass relation and the compiler's memory/register/state relation in
the resulting statement. A caller reaching the reporting cut must supply that
state relation; a compilation equation must identify the selected assembly.

`PrimitiveCalls.runtime_contract` relates stock external calls to individual
byte/TLS/library effects and requires local progress. `StockCalls` proves the
step and finite-run connection; `CompiledReporting` supplies source progress from
the existing reporting proof. Neither contract assumes whole-call safety or a
decoded result. Finite prefixes include failed and short completed I/O calls.
A prefix alone never establishes successful return. The source model retains
arbitrary instruction-boundary loss and partial-call loss. Stock compiler traces
contain completed atomic external calls, so asynchronous loss during a partially
completed call remains an unsupplied connection. Do not remove those source
transitions or promote this conditional model to a deployed guarantee.

The compiler relation at the reporting call remains an explicit premise. In
particular, whole-program initial simulation does not supply the helper's
physical `argc`/`argv`, descriptors or a matched reporting cut. Runtime effect
implementations, that caller producer, partial-call loss and the retained GCC
deployment remain original correspondence obligations.

## certificate: Check the concrete backend output

Make register allocation's candidate an explicit function argument to the pinned
allocation proof. Preserve every validation check and every semantic invariant;
the theorem must quantify over that argument. The candidate generator and term
printer remain untrusted. Check the resulting pass relation for the current
complete helper in the kernel, including the allocation validator's result.
Do not add an axiom identifying the external allocator's answer, accept a hash
as a compilation equation, or disable conversion checking.

Retain the upstream notices and licensing for adapted compiler proofs. Generate
the adaptation from the pinned source with an exact, reviewable change. Reuse
the unchanged compiled compiler dependencies and source reporting evidence.
[§DA-compiled-reporting](../decisions/architectural/DA-compiled-reporting.md#da-compiled-reporting-instantiate-and-consume-the-reporting-compiler-proof) records the backend and runtime interface choices.

Use the eight required lowering passes from Clight2 through Cshmgen, Cminorgen,
Selection, RTLgen, validated allocation, Linearize, Stacking and Asmgen. Omit
optional optimizations. Select ELF x86-64 calling conventions explicitly in the
calling-convention and stack-layout clients, leaving the retained compiler and
source-semantics foundation unchanged. Fixed heuristics remain subject to the
original validators. Transparent solver interfaces and termination witnesses
permit ordinary checked computation. The replacement bounded iterator has a
kernel-checked equality to the original iterator; proof-script adaptations
preserve the compiler theorem statements.

Retain separately checked lowering, allocation and assembly results, then
compose their equations symbolically. All computation uses ordinary checked
proof terms; no unchecked conversion or compiler-correctness axiom is permitted.
The proposed record is not accepted automatically. Freeze the complete compiled
declaration inventory, full types, transitive foundations, dependency identities,
independent kernel check and rejected corrupt-allocation/runtime-root controls
in `assurance/reporting-compiler.json.gz`. Reuse matching evidence. Generated
assembly text is an untrusted presentation, not a certified ELF artifact.

`assurance/reporting-compiler-before.json.gz` preserves the prior reporting
records, aggregate command and checker. The explicit amendment permits only the
two added compiler-gate invocations and their fingerprint adapter. It changes
one operational source-record fingerprint and the connection's corresponding
metadata, preserving every earlier theorem, foundation and compiled artifact.
Compiler kernel receipts bind actual proof files and check tools; operational
record formatting does not invalidate their proof identities.

The logical foundations are classical choice/decidability, functional
extensionality, proof irrelevance and equality transport, together with the
strict importer's recorded definitional UIP. CompCert's standard external and
inline-assembly relations and their properties remain explicit assumptions.
The audit rejects additional foundations, including the original external
allocator answer and an unresolved calling-convention parameter. These logical
and compiler interfaces do not implement Linux effects.

## runtime: Preserve a root for thread-local errno

Stock CompCert external-call compatibility cannot return an existing private
block that is absent from every argument and preserved symbol. Its injection
property forbids creating a mapping for an already allocated, unmapped source
block. An interface merely assuming that `__errno_location` returns such a block
may therefore have inconsistent premises. Reachability restrictions alone do
not solve this issue.

Represent the trusted helper's current thread with a public logical `errno`
object supplied by the runtime unit. Retain the complete helper's actual
function definitions and recheck their reporting consumers in that composed
global environment. Tie the owned TLS cell to that preserved symbol. This is
an address interface for the per-thread runtime view; it does not replace native
TLS with an ordinary global or prove the loader's interpretation. The actual
libc/TLS, process/thread and loader producers remain mandatory. Require an
inhabited owned reporting input at the rooted cell before promoting this
conditional compiler connection.
