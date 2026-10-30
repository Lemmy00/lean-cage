# LeanCage

LeanCage is a reusable sandbox for AI agents, built in Lean 4 and designed for
end-to-end proofs of correctness and isolation.

The goal is to run untrusted native programs on Linux with explicit, checked
security guarantees. We start from a small part of Bubblewrap's behavior and
grow a verified Lean implementation, using Velvet where it helps with imperative
proofs. The roadmap extends through Linux enforcement, executable correspondence,
and software-observable hardware side channels.

**Status: M1 filter/launch proof slice complete.** The selected x86-64 filter
has kernel-checked decoder/bounds and launch-order proofs, an audited theorem
manifest, and a Lean/native driver demonstrated in an isolated Linux VM. All 13
VM cases pass, including allowed/denied syscalls and setup failures. This is an
experimental filter-loading slice; full confinement and production security
remain later milestones.

- [Plan and milestones](docs/roadmap.md)
- [M1 review and M2/M3 readiness](docs/reviews/M1-readiness.md)
- [Functional specification](docs/functional-spec/README.md)
- [Architecture](docs/architecture/README.md)
- [First filter and launch boundary](docs/architecture/AR-filter-slice.md)
- [Decoder proofs and audit](docs/architecture/AR-filter-decoder.md)
- [Launch proofs, Linux binding, and VM](docs/architecture/AR-m1-launch.md)
- [Proof obligations and assumptions](docs/functional-spec/FS-assurance.md)
- [Development guide](docs/development.md) and [agent rules](AGENTS.md)

With [elan](https://github.com/leanprover/elan), Python 3, Bash, Git, curl, tar,
GNU coreutils, and a C compiler/Linux headers available on Linux x86-64:

```sh
./scripts/check.sh
```

The first run downloads checksum-pinned Grund 0.20.0 into this repository's
ignored `.tools/` directory and fetches the pinned Lean dependencies. No global
Grund installation or agent settings are changed. The wrapper supports GNU/Linux
on x86_64 and aarch64; the initial setup is validated on x86_64.

The gate checks proofs, compiles the native driver, and validates the archived
VM evidence against current source identities. For a fresh VM replay on the
recorded Ubuntu 24.04 host, use `python3 scripts/run_m1_vm.py --prepare`; local
downloads/builds stay under `.tools/`. See the [development guide](docs/development.md).

The development workflow follows [§AR-tooling](docs/architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local). Linux enforcement and native
compiler/runtime/FFI correspondence remain assumptions. Passing Grund checks
establishes documentation consistency; it does not establish sandbox security.

Licensed under [Apache 2.0](LICENSE).
