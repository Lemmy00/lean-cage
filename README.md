# LeanCage

LeanCage is a reusable sandbox for AI agents, built in Lean 4 and designed for
end-to-end proofs of correctness and isolation.

The goal is to run untrusted native programs on Linux with explicit, checked
security guarantees. We start from a small part of Bubblewrap's behavior and
grow a verified Lean implementation, using Velvet where it helps with imperative
proofs. The roadmap extends through Linux enforcement, executable correspondence,
and software-observable hardware side channels.

**Status: M1–M3 accepted for their stated conditional profiles.** M3 adds an offline Dash/Python workspace,
immutable runtime, private copied inputs, controlled I/O/export, confined
descendants, cgroup limits and real check/run/report commands. Its model proofs
and source-bound VM evidence are documented in the [M3 review](docs/reviews/M3-handoff.md).
Native/Linux/compiler/loader correspondence remains M4; confidentiality and
hardware-channel security remain later obligations. No production profile is
certified by these conditional model results and tests.

- [Run LeanCage: build, VM replay, and CLI commands](docs/running.md)
- [How the milestones compose into one product](docs/architecture/AR-product.md)
- [Plan and milestones](docs/roadmap.md)
- [Preserved M1 readiness review](docs/reviews/M1-readiness.md)
- [M2 lifecycle and handoff](docs/reviews/M2-handoff.md)
- [M3 workspace and handoff](docs/reviews/M3-handoff.md)
- [M3 main review and correction](docs/reviews/M3-main-review.md)
- [Current M4 continuation and review boundary](docs/roadmap.md#m4next-current-m4-continuation)
- [M4 continuation assignment](M4-CONTINUE.md)
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
(cd m3 && lake build leancage)
m3/.lake/build/bin/leancage validate-policy profiles/m3/example-policy.json
```

This builds the current CLI and checks a sample policy without executing guest
code. On a prepared checkout, `python3 scripts/run_m3_vm.py --development` runs
the assembled controller/helper and real shell/Python workloads in the disposable
VM. The [running guide](docs/running.md) gives preparation and result paths.
The supported `check`, `run` and `report` commands currently operate inside that VM.

Run the proof/build gate separately:

```sh
./scripts/check.sh
```

The full implemented M4 chain has a separate gate, `./scripts/check_m4_all.sh`.
M4.1 feasibility and local reporting/controller proofs through initialization
are recorded. Parent composition repair has passed independent statement/focused
review; its [acceptance record](assurance/m4-parent-validation.json) tracks the
aggregate gate. Early Lean/Linux connection attempts expose reproducible blockers;
full M4 remains open. See the [independent repair review](docs/reviews/M4-parent-independent-review.md)
and [connection feasibility](docs/architecture/AR-m4-routes.md).

The first run downloads checksum-pinned Grund 0.20.0 into this repository's
ignored `.tools/` directory and fetches the pinned Lean dependencies. No global
Grund installation or agent settings are changed. The wrapper supports GNU/Linux
on x86_64 and aarch64; the initial setup is validated on x86_64.

The gate checks all three proof packages, compiles the native drivers, and validates
archived VM evidence against current source identities. For a fresh VM replay on the
recorded Ubuntu 24.04 host, use `python3 scripts/run_m1_vm.py --prepare`; local
downloads/builds stay under `.tools/`. For M2 use `python3 scripts/run_m2_vm.py --prepare`; this builds its separate
capable kernel and executes workloads only in the disposable VM. For M3 run
`python3 scripts/run_m3_vm.py --prepare`, then `python3 scripts/run_m3_vm.py` to
build and replay its separate runtime/workspace profile. See the
[development guide](docs/development.md).

The development workflow follows [§AR-tooling](docs/architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local). Linux enforcement and native
compiler/runtime/FFI correspondence remain assumptions. Passing Grund checks
establishes documentation consistency; it does not establish sandbox security.

Licensed under [Apache 2.0](LICENSE).
