# AR-m1-launch: Launch model, Linux driver, and isolated demonstration

Implement [§FS-filter-loading.installation.model](../functional-spec/FS-filter-loading.md#installationmodel-executable-launch-semantics-and-proof-obligations) and
[§FS-filter-loading.installation.binding](../functional-spec/FS-filter-loading.md#installationbinding-first-concrete-linux-driver) using the existing portable stages and
the actual decoder from [§FS-filter-loading.input.correctness](../functional-spec/FS-filter-loading.md#inputcorrectness-decoder-proof-boundary).

## model: Total transitions and trace evidence

`LeanCage/Launch/Model.lean` implements stage/event transitions and finite replay.
It accepts an independently computed validation verdict and represents failed
calls, interruption, effective cancellation, contract violation, and external
termination. Invalid event/state combinations have no transition. This does not
remove environment outcomes: all documented outcomes of the expected operation
remain possible. Native effect honesty and the entry conditions are assumptions.

`LeanCage/Proofs/Launch.lean` establishes receipt preservation, installation before
exec attempts and image replacement, terminal failure, and an inhabited success
trace. The decoder linkage must use its actual result, not a supplied conclusion.
The results state partial correctness; arbitrary process termination is permitted.

`SuccessfulHistory` assigns each successful stage its exact ordered prefix;
`executed_trace_exact` proves that every executed history equals `successTrace`.
`replay_iff_reaches` connects total executable replay to inductive reachability.
`validationVerdict_iff` and `invalid_input_never_executes` connect this model to
the independent mathematical byte predicate and actual decoder.

## binding: Small native boundary

The Lean driver decodes before invoking the native binding. Native preparation
checks the trusted static ELF, constructs private fixed-width filter storage, and
prepares argv/environment and an error-only close-on-exec pipe. The forked child
does no Lean runtime work and uses the exact no-new-privileges/install/exec order.
No success notification or allocation occurs after installation before exec.
Failure reporting may itself fail; the child exits without another exec attempt.

Every native return convention, errno, storage lifetime, pipe handle, signal
disposition, and wait outcome must be mapped explicitly to
[§FS-filter-loading.installation.failure](../functional-spec/FS-filter-loading.md#installationfailure-terminal-failures-without-rollback-claims). The C implementation and compiled
executable remain assumed to implement this call map; differential tests are
supplemental evidence, not a source-refinement proof.

The implementation is `LeanCage/Linux/Launch.lean`, `M1Main.lean`, and the original
`native/leancage_m1.c`. `PreparedFilter` carries the actual Lean decoder equality.
`launch` calls the binding only on that success branch. The file adapter reads
at most 32769 bytes (one above the rejection ceiling); it closes the input before
native entry. Its IO/filesystem/runtime correspondence is assumed, separately
from the pure byte decoder proof. Only trusted stable inputs occur in the test
profile; this is not a hostile filesystem ingestion API.

| Concrete boundary | Contract and model observation |
|---|---|
| Lean decode; native profile, static ELF, buffer/entry preparation | `validationAccepted` only when all prerequisites hold; rejection is terminal before the model's setup segment |
| `prctl(PR_SET_NO_NEW_PRIVS, 1UL, 0UL, 0UL, 0UL)` returns exactly 0 | `noNewPrivilegesSet`; this does not claim that inherited privileges were dropped |
| `prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &program, 0UL, 0UL)` returns exactly 0 | `filterInstalled` under the Linux contract for the same thread and exact program |
| One immediate `execve` invocation | `execAttempted`; successful replacement is `execSucceeded`, never a C return |
| Either setup call or exec returns -1 with errno 1..4095 | Terminal `osError`, except errno 4 maps to terminal `interrupted`; no child retry |
| Unexpected return convention | Terminal `contractViolation`; error-only report followed by `_exit(125)` |
| Effective cancellation or external termination before replacement | Abstract terminal cancellation/termination; the demo tests SIGTERM, not a cancellation API |

`sock_filter` widths, offsets, size/alignment and `sock_fprog` LP64 layout have
compile-time assertions. Fields are copied explicitly from accepted bytes into
nine stack instructions. Path, argv, environment, instruction array and `fprog`
remain live across both `prctl` calls and until exec/failure. Fork gives the
single-threaded child private copy-on-write storage; it uses no Lean API or
allocator. Shared-file mutation, hostile tracers, or hostile pre-reset handlers
violate the stated entry profile and remain open obligations.

The child masks signals, resets native Linux handlers 1..64 except SIGKILL and
SIGSTOP (including NPTL-reserved handlers), unmasks, and checks
`PR_GET_SECCOMP == 0`. Resetting uses the explicit x86-64 kernel sigaction layout;
its ABI/correspondence is assumed. The target is an absolute, NUL-free static
native ET_EXEC ELF; bounded ELF-header/program-header reads reject interpreters,
wrong widths/ABI and out-of-file load regions. This is a scoped trusted-image
check, not a verified adversarial ELF loader. It does not close the file-to-exec
race; file stability is an explicit premise.

An error-only `pipe2(O_CLOEXEC)` is allocated before fork. Parent owns the read
end; child owns the write end. Each closes the other end; successful exec closes
the writer. Child failure makes one bounded write and exits even on short/failed
reporting. Parent handles partial reports, read/close errors, interrupted reads,
and `waitpid` separately; parent-only retry does not retry a child setup call.
Linking with `-Wl,-z,now` resolves PLT bindings before the child segment.

The packed result's low bytes are kind (0 guest exit, 1 errno, 2 signal,
3 contract/supervision error, 4 interruption) and phase (1 preflight, 2 NNP,
3 install, 4 exec, 5 wait, 6 protocol). Bits 16..47 contain errno/status/signal;
bits 48..55 are historical receipt bits (1 validation, 2 NNP, 4 installation,
8 exec attempt) for reported child failures. They do not claim rollback.
An empty pipe alone does not prove exec success; signal/protocol/wait results
can be ambiguous about guest entry. Supervisor errors are outside the child
transition model and must not be reclassified as proof of no guest execution.
Guest exit 125 is reserved and reported as protocol ambiguity in this fixture.

Modes 1 and 2 inject actual invalid-argument NNP/install calls; mode 3 terminates
setup; modes 4 and 5 request the guest's x32/i386 probe. Mode 0 is the ordinary
profile. Unsupported modes fail preflight. The native kernel/marker check prevents
accidental host use; it is not VM attestation or validation of every entry premise.

## vm: Disposable Linux profile and evidence

Build the existing Linux 6.18.59 reference from checksum-pinned upstream source.
Use a project-local QEMU installation with software CPU emulation, one vCPU,
bounded memory, no networking, no host mounts, and an ephemeral initramfs.
No host filter, kernel reconfiguration, privileged host workload, or unrelated
process management is permitted. Record all relevant artifact/configuration and
virtual CPU/firmware identities required by [§AR-linux.platform](AR-linux.md#platform-isolated-integration-profile).

`scripts/run_m1_vm.py --prepare` verifies `tests/vm/bootstrap-pins.json`, extracts
Ubuntu packages locally, and builds fresh Linux sources using the checked full
configuration. `kernel.fragment` records principal choices; the full configuration
is authoritative. Kernel source/image/configuration and relevant test tools
are identified in `assurance/m1-vm-evidence.json`. Preserve any intended upstream
pin change as a deliberate review, never an automatic apt upgrade.

The newc initramfs writer encodes device nodes directly in the archive; no host
root access or `mknod` is needed. Trusted PID 1 mounts proc/sysfs only inside the
VM, drops the launcher to UID/GID 65534 with no supplementary groups, and runs
the 13 cases. The test memory budget is 2048 MiB to permit Lean's startup virtual
stack reservation, one vCPU, and a 180-second timeout. It makes no timing or
resource-confinement guarantee. Test tools/configuration/images live in ignored
`.tools/m1vm`; the small structured evidence and raw log are retained.

The guest must demonstrate direct `getpid` success, direct `getppid` blocked with
`EPERM`, and no guest execution on malformed input or failed setup. Inject actual
no-new-privileges/install/exec errors and record exit/diagnostic evidence. Keep
the pinned source, resolved configuration, images, commands, and transcripts
replayable. A VM demonstration does not establish hardware confidentiality.

## audit: Preserve decoder claims and extend the assurance gate

Extend [§AR-filter-decoder.audit](AR-filter-decoder.md#audit-declaration-type-and-axiom-gate) with launch declarations and native/source/test
identities after reviewing their full types and transitive axioms. Preserve the
M1.2 theorem statements and axiom sets. Record model proofs, concrete call mapping,
native tests, assumed kernel enforcement, and open native correspondence separately
under [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record). M1 is complete only when every exit criterion in
[§RM-roadmap.m1](../roadmap.md#m1-first-executable-proof-slice) has actual evidence.

The historical `assurance/filter-decoder.json` filename now covers all M1 proofs,
sources and test evidence. An independent `assurance/m1.2-decoder-claims.json`
preserves the original 18 full decoder types/axiom sets and the prior manifest
identity. The audit rejects any departure from either record. This extends the
gate without refreshing decoder statements to accommodate a new implementation.
`scripts/run_m1_vm.py --check-evidence` validates the archived passing transcript
and exact source hashes, including its verifier; it does not boot a VM or
certify current native compilation. Replay the VM explicitly when sources change.
