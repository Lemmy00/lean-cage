# Changelog

## Unreleased

- Establish the M0 specification, staged roadmap, assumption register, and agent
  development rules under [§RM-roadmap.m0](roadmap.md#m0-specification-and-development-foundation).
- Pin the Lean/Velvet foundation and local Grund workflow under [§AR-tooling](architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local).
- Add the M1.1 pinned source/ABI map, canonical filter, launch/failure contracts,
  and compiled Lean interfaces under [§AR-filter-slice.contracts](architecture/AR-filter-slice.md#contracts-lean-declarations-and-downstream-ownership). Check the
  reference program on 14 architecture/syscall inputs without OS effects.
- Implement the M1.2 pure byte decoder, kernel-checked acceptance/rejection,
  unsigned-width and count/index bounds, a successful input witness, malformed
  and exhaustive single-byte checks, and source-bound declaration/type/axiom
  evidence under [§AR-filter-decoder](architecture/AR-filter-decoder.md#ar-filter-decoder-byte-decoder-proofs-and-executable-evidence-audit).
- Implement M1.3–M1.5 under [§AR-m1-launch](architecture/AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration): total launch transitions, exact-order
  and terminal-failure proofs linked to the actual decoder, an original Lean/C
  native driver, and 13 passing isolated Linux VM cases. Preserve all M1.2
  decoder statements/axioms and extend the source-bound audit and claim register.
  Native/Linux correspondence and full sandbox isolation remain open.

- Independently review the M1 statements, native boundary, evidence and VM replay;
  preserve raw serial bytes in Git and record the [readiness review](reviews/M1-readiness.md).
  Expand [§RM-roadmap.m2](roadmap.md#m2-verified-launcher-lifecycle) and [§RM-roadmap.m3](roadmap.md#m3-useful-offline-workspace-sandbox) into bounded packages, beginning with
  lifecycle contracts and a capable isolated profile; retain M4/M5 obligations.

- Implement M2.1–M2.7 under [§FS-lifecycle](functional-spec/FS-lifecycle.md#fs-lifecycle-m2-owned-launcher-lifecycle) and [§AR-lifecycle](architecture/AR-lifecycle.md#ar-lifecycle-m2-controller-native-helper-and-evidence): a decoded fixed plan,
  sealed static executable, fresh root helper, owned PID/mount/net/IPC/UTS setup,
  full credential/capability reduction, trusted exec observation, pidfd
  supervision, descendant teardown, cancellation races and explicit unknown
  reports. Add general bytecode semantics, conditional lifecycle proofs, a
  capable separate kernel and 43 VM cases; preserve all M1 proofs and original
  evidence. The full handoff gate and artifact comparison pass. Native/Linux correspondence,
  M3 authority and M5 hardware channels remain open.

- Review M2 with a fresh 43-case replay; make archived evidence checks portable
  across checkout paths, bind the dependent toolchain pin, and add four regression
  tests under [§AR-lifecycle.audit](architecture/AR-lifecycle.md#audit-evidence-schema-and-replay-gates).
  Define [§RM-roadmap.m3.entry](roadmap.md#m3entry-next-assignment-m31-authority-and-workload-contract) as the next bounded contract assignment, including
  workspace authority, runtime closure, private reports and correspondence research.
- Give complete theorem-environment queries a shared 180-second deadline after
  observing a CI timeout at the former 60-second M1 limit. Preserve every theorem,
  type/axiom comparison and fail-closed timeout under [§AR-filter-decoder.audit](architecture/AR-filter-decoder.md#audit-declaration-type-and-axiom-gate).
