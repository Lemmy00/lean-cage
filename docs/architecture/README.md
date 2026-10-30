# Architecture

These are design contracts for the staged implementation. Only the tooling and
Lean dependency foundation are implemented at M0.

| Contract | Subject |
|---|---|
| [§AR-core](AR-core.md#ar-core-separate-portable-security-contracts-from-platform-mechanisms) | Portable policy, state, effects, and observations |
| [§AR-linux](AR-linux.md#ar-linux-connect-a-lean-launcher-to-real-linux-enforcement) | Linux enforcement, OS bindings, and pinned reference |
| [§AR-verification](AR-verification.md#ar-verification-compose-explicit-refinement-and-security-arguments) | Proof composition, audits, and executable correspondence |
| [§AR-tooling](AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local) | Local tooling, pins, and development checks |
