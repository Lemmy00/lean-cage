# DA-grund: Trial pinned Grund inside this repository only

**Status: accepted.** Use the canonical goals/specifications/requirements/
architecture/decisions/roadmap layout, readable slug IDs, marked citations, and
GitHub links. Follow [§AR-tooling](../../architecture/AR-tooling.md#ar-tooling-keep-development-reproducible-and-project-local) to support [§FS-assurance.evidence](../../functional-spec/FS-assurance.md#evidence-required-claim-record).

## rationale: Give agents stable context

Stable references and checked citation directions make changes easier to trace.
A custom Lean line-comment profile connects future code and proofs to the
specification. The integration test must demonstrate that this profile works.

## limits: Documentation tooling is not the verifier

Pin Grund 0.20.0 locally, leave other projects and global settings untouched, and
evaluate its usefulness during development. A clean documentation graph is not
evidence that a theorem states the right property or that Linux enforces it.
