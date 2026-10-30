# LeanCage

LeanCage is a reusable sandbox for AI agents, built in Lean 4 and designed for
end-to-end proofs of correctness and isolation.

The goal is to run untrusted native programs on Linux with explicit, checked
security guarantees. We start from a small part of Bubblewrap's behavior and
grow a verified Lean implementation, using Velvet where it helps with imperative
proofs. The roadmap extends through Linux enforcement, executable correspondence,
and software-observable hardware side channels.

**Status: M0 foundation.** This repository contains the specification, development
rules, project-local Grund tooling, and a pinned Lean/Velvet build. There is no
runnable sandbox or proved isolation guarantee yet.

- [Plan and milestones](docs/roadmap.md)
- [Functional specification](docs/functional-spec/README.md)
- [Architecture](docs/architecture/README.md)
- [Proof obligations and assumptions](docs/functional-spec/FS-assurance.md)
- [Development guide](docs/development.md) and [agent rules](AGENTS.md)

With [elan](https://github.com/leanprover/elan), Python 3, Bash, Git, curl, tar,
and GNU coreutils available:

```sh
./scripts/check.sh
```

The first run downloads checksum-pinned Grund 0.20.0 into this repository's
ignored `.tools/` directory and fetches the pinned Lean dependencies. No global
Grund installation or agent settings are changed. The wrapper supports GNU/Linux
on x86_64 and aarch64; the initial setup is validated on x86_64.

The development workflow follows [§AR-tooling](docs/architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local). Passing Grund checks establishes
documentation consistency; it does not establish sandbox security.

Licensed under [Apache 2.0](LICENSE).
