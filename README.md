# LeanCage

LeanCage is a reusable sandbox for AI agents, built in Lean 4 and designed for
end-to-end proofs of correctness and isolation.

The goal is to run untrusted native programs on Linux with explicit, checked
security guarantees. We start from a small part of Bubblewrap's behavior and
grow a verified Lean implementation, using Velvet where it helps with imperative
proofs. The roadmap extends through Linux enforcement, executable correspondence,
and software-observable hardware side channels.

**Status: M1 and M2 lifecycle proof slices complete for their stated profiles.**
M2 adds a decoder-controlled Lean launcher, a fresh VM-only native helper, sealed
executable handles, namespace/credential setup, descendant supervision and
cancellation, plus general fixed-filter semantics. Its conditional model proofs
and source-bound VM evidence are recorded in the [M2 review](docs/reviews/M2-handoff.md).
Full workspace confinement, native/Linux correspondence and hardware-channel
security remain later milestones.
The next assignment is the [M3.1 authority and workload contract](docs/roadmap.md#m3entry-next-assignment-m31-authority-and-workload-contract).

- [Plan and milestones](docs/roadmap.md)
- [Preserved M1 readiness review](docs/reviews/M1-readiness.md)
- [M2 lifecycle and handoff](docs/reviews/M2-handoff.md)
- [Functional specification](docs/functional-spec/README.md)
- [Architecture](docs/architecture/README.md)
- [First filter and launch boundary](docs/architecture/AR-filter-slice.md)
- [Decoder proofs and audit](docs/architecture/AR-filter-decoder.md)
- [Launch proofs, Linux binding, and VM](docs/architecture/AR-m1-launch.md)
- [Proof obligations and assumptions](docs/functional-spec/FS-assurance.md)
- [Development guide](docs/development.md) and [agent rules](AGENTS.md)

With [elan](https://github.com/leanprover/elan), Python 3, Bash, Git, curl, tar,
GNU coreutils, and a C compiler/Linux headers/static libc development files
available on Linux x86-64:

```sh
./scripts/check.sh
```

The first run downloads checksum-pinned Grund 0.20.0 into this repository's
ignored `.tools/` directory and fetches the pinned Lean dependencies. No global
Grund installation or agent settings are changed. The wrapper supports GNU/Linux
on x86_64 and aarch64; the initial setup is validated on x86_64.

The gate checks both proof packages, compiles the native drivers, and validates
archived VM evidence against current source identities. For a fresh VM replay on the
recorded Ubuntu 24.04 host, use `python3 scripts/run_m1_vm.py --prepare`; local
downloads/builds stay under `.tools/`. For M2 use `python3 scripts/run_m2_vm.py --prepare`; this builds its separate
capable kernel and executes workloads only in the disposable VM. See the
[development guide](docs/development.md).

The development workflow follows [§AR-tooling](docs/architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local). Linux enforcement and native
compiler/runtime/FFI correspondence remain assumptions. Passing Grund checks
establishes documentation consistency; it does not establish sandbox security.

Licensed under [Apache 2.0](LICENSE).
