# M2 lifecycle implementation and handoff review

This review covers [§RM-roadmap.m2](../roadmap.md#m2-verified-launcher-lifecycle) and the versioned contract [§FS-lifecycle](../functional-spec/FS-lifecycle.md#fs-lifecycle-m2-owned-launcher-lifecycle) for
`leancage-m2-linux-6.18.59-root-v1`. It is an implementation/statement/evidence
review, not an independent native verification or a production certification.

**Verdict: M2.1–M2.7 accepted for the stated conditional lifecycle profile.**
The implementation gate passed on 2026-10-30. The independent readiness pass on
2026-10-31 also checked a relocated checkout and corrected the archive path and
M2 toolchain coverage issues described below.
The proof/test boundary is [§FS-assurance.lifecycle](../functional-spec/FS-assurance.md#lifecycle-m2-lifecycle-and-filter-semantics-claim-record). The M1 core, native driver,
kernel/configuration and raw demonstration remain unchanged. The original full
theorem manifest is preserved byte-for-byte as `assurance/m1-reviewed-baseline.json`.

## Work packages in order

| Package | Delivered output | Acceptance evidence |
|---|---|---|
| M2.1 | [§FS-lifecycle](../functional-spec/FS-lifecycle.md#fs-lifecycle-m2-owned-launcher-lifecycle) initial/post/failure/outcome/observation contracts; [§AR-lifecycle.entry](../architecture/AR-lifecycle.md#entry-disposition-of-every-m1-entry-premise) premise inventory; [§DA-m2-profile](../decisions/architectural/DA-m2-profile.md#da-m2-profile-fresh-root-helper-and-owned-pid-namespace-for-m2) and source/effect map | Design and native boundary reviewed before enlarging the implementation; root helper, fixed plan, sealed handle, trusted init and explicit M4 ledger |
| M2.2 | Separate full Linux 6.18.59 configuration and fresh kernel build; capable disposable VM | Namespace, Unix/IPv4, SysV IPC and cgroup CPU/memory/pids positive controls; original M1 profile preserved |
| M2.3 | Actual decoder-controlled plan, private/sealed bounded ELF snapshot, allowlisted stdio, close_range, fixed argv/environment/cwd and signal bootstrap | Inherited file/directory/socket aliases; stdin/umask/signal checks; bad ELF, symlink, noexec, missing profile, changed plan and external tracer rejection; short I/O/report failures |
| M2.4 | PID/mount/net/IPC/UTS setup; private mount propagation/procfs; groups, all UID/GID forms, bounding/ambient/E/P/I capabilities and NNP reduction | Conditional reachable launch invariant; namespace/mount/handle/credential/NNP/filter/exec failure boundaries; actual guest credential/capability assertions; existing filter rejection including a masked prctl query |
| M2.5 | pidfd-owned init, trusted TRACEEXEC, guest exit/signal/setup/cancel/unknown tags, descendant reaping and namespace teardown | Exit 125, leader re-exec, fork/exec, double-fork/setsid survivor, setup signal, stopped guest, cancel before/after exec, deadline, helper/controller/init death and both helper/init pre-arming races; sentinel survives every case |
| M2.6 | Exact plan history, decoder linkage, all reachable safety/descendant invariants and M1 event refinement; unsigned bytecode semantics | Universal theorem types/axioms, concrete success/failure/race witnesses and 33 Lean guard commands; native x32/i386 denial alongside useful allowed syscalls |
| M2.7 | Strict source/artifact/guest-image/schema/transcript evidence; complete theorem inventory and preserved M1 statements | `assurance/m2-claims.json`, `assurance/m2-vm-evidence.json`, raw transcript and full gate; the full gate passed |

## Statement and assumption review

The 31 named authored theorems and all generated/project theorem declarations are
enumerated with full types and exact axiom sets. The logical axiom union is only
`propext`, `Classical.choice`, and `Quot.sound`. The main safety statement quantifies
over every reachable state from an empty initial state. Success cannot skip a
stage; invalid input cannot enter; every live member retains the modeled scope,
complete credential record, NNP and filter. Errors, interference, reporting loss and cancellation remain
explicit transitions. Cancellation requests may precede successful exec; only an
actual death observation removes the scope. Historical restrictions are retained
after failure/death instead of asserting rollback.

The general bytecode theorem quantifies over arbitrary UInt32 architecture and
syscall words. It uses instruction-step lemmas and kernel reduction, not native
evaluation, sampled inputs, or a desired-action premise. The singleton program
tag explains why the decoder-linked corollary has no other program branch.
Successful lifecycle histories project to the unchanged M1 success trace; this
is an event refinement, not a theorem about C, execveat or Linux machine execution.

Credential IDs are UInt32; capabilities and signal masks are UInt64; startup
thread count is UInt32. UID/GID records include real/effective/saved/filesystem
forms, supplementary groups and all five capability sets. Native checks read back
the FSUID/FSGID as well as real/effective/saved IDs. Initial credential/signal
snapshots are absent, not assumed normalized. Clean startup signals are historical;
arbitrary guest signal handlers after entry are not forbidden by the theorem.

The model's birth identities are logical tokens; native PIDs/fds have actual Linux
widths, reuse and lifetime rules, handled by pidfds and unreaped direct children.
The model does not model arbitrary external victims or a workspace authority
policy. Outside-signal/escape attempts remain in its event vocabulary without
claiming that the model proves every syscall effect is confined. The VM root tree
is public fixture data. Filesystem aliases, cross-process/IPC/network authority,
dynamic shell/Python runtimes and resource budgets remain M3. The exact selected
namespace/credential/seal/ptrace/signal effects are OS contracts; each has an open
native/Linux refinement entry in [§AR-lifecycle.correspondence](../architecture/AR-lifecycle.md#correspondence-m4-obligation-ledger). The trusted root
operator and helper/init images remain environmental premises.

Private error/result pipes carry the actual supervision decisions. The VM
console carries public fixture diagnostics and guest output; a future caller
must not treat arbitrary guest console lines as authenticated outcomes. M3.6
owns the reusable external result/report API and its separation from guest I/O.

Liveness additionally needs fair scheduling, terminating kernel calls, SIGKILL
delivery and sufficient supervision resources. No wall-clock or end-to-end
termination theorem is claimed. Hardware/timing/cache/contention/speculation
confidentiality remains [§FS-observations.hardware](../functional-spec/FS-observations.md#hardware-software-observable-channels).

## Evidence and reproducibility

All experiments run in the disposable RAM-only TCG VM, with no host mount, NIC or
persistent disk. Raw serial bytes are preserved by `.gitattributes`. Every passing
case requires exact typed results, guest markers/absence where applicable, observed
owned-scope extinction and survival of an unrelated VM sentinel. Error injection
uses actual failing calls for namespace/mount/descriptor/credential/NNP/filter/exec
boundaries. Short/absent reports, deterministic cancellation/death and path rename
are explicit fixture injections, not claims that random faults were observed.

Reproduce from the recorded Ubuntu 24.04 x86-64 host:

```sh
./scripts/grund.sh fmt --write
./scripts/check.sh
python3 scripts/run_m2_vm.py --prepare
python3 scripts/run_m2_vm.py --check-evidence
python3 scripts/run_m2_vm.py --check-artifacts
```

Preparation verifies pinned upstream archives/packages, builds a new kernel under
`.tools/m2vm`, and keeps M1 unchanged. Replay without `--prepare` uses that kernel
and rebuilds the guest image. The ordinary handoff gate compiles native code and
checks archived evidence; only the explicit replay executes workloads. Current
artifact checking separately compares every recorded binary/config/image hash.
SHA-256 identifies artifacts; it does not certify compilation or kernel behavior.

The proof auditor checks the full 445-theorem M1 baseline as well as M2; its normal
path never regenerates expectations. The root M1 manifest needs reviewed source
fingerprint changes only for shared guidance/check additions; its 43 named claims,
all theorem types/axioms, source/tool pins and original VM evidence are preserved.

## Final validation

- `./scripts/check.sh`: exit 0; Grund ordinary/full/format/guidance checks, both
  Lean packages, native compilation, **42 Python tests** (21 M1 + 21 M2), and
  **91 Lean guard commands** (58 M1 + 33 M2) all pass.
- Statement/axiom audit: **31 named M2 claims / 274 total M2 theorem declarations**,
  **45 source/dependency/evidence identities**, and every one of the original
  **445 M1 theorem types/axiom sets** preserved. The root M1 audit still checks its
  43 named claims and 39 identities. No custom, unfinished or compiler-trust axiom
  is accepted.
- Fresh capable-kernel VM replay: **43/43 cases pass**, with namespace, Unix/IPv4,
  SysV IPC and cgroup CPU/memory/pids positive controls. All owned scopes are gone
  and the unrelated sentinel survives each case.
- `python3 scripts/run_m2_vm.py --check-artifacts`: all **64 recorded artifact
  hashes** match available current binaries/configuration/image/runtime/tools.
- The original M1 raw VM record still validates **13/13 archived cases** against
  unchanged source identities; M1 is not counted as a new VM replay here.

## Independent readiness corrections

The original M2 gate passed at the author's checkout but interpreted archived
absolute emulator paths as paths belonging to the validating checkout. Reproducing
the check under a different checkout root failed with `Unpinned M2 emulator location`.
The archive validator now checks the exact command/environment/artifact layout
against its recording root; current-artifact comparison maps project artifacts to
the current checkout. Required flags and source/artifact identities are preserved.
Three regressions cover relocation, mixed roots and current artifact resolution.

The M2 source inventory also omitted `m2/lean-toolchain`. It is now hashed, and the
auditor rejects a different pin before building. A fourth regression checks this
boundary. No Lean statement, proof, native helper or workload behavior changed in
these corrections. Source/evidence fingerprints were updated only after reviewing
these changes and rerunning the VM; theorem types and axiom sets remain unchanged.
The readiness replay uses the existing hash-checked M2 kernel, not a new kernel
build. The implementation's original source/kernel build is historical evidence.

## Remaining obligations and next assignment

All eight entries in [§AR-lifecycle.correspondence](../architecture/AR-lifecycle.md#correspondence-m4-obligation-ledger) remain open for M4; no manual
source map or VM case closes them. M3.1 must specify the actual runtime/workspace
authority and shell/Python closure before implementing M3.2–M3.7. Do not reuse the
M2 public fixture root or the broad deny-getppid filter as that policy.
