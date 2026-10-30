# GRUND-trust: Capability-independent containment for AI agents

More capable AI systems can produce and execute arbitrary programs. Trust in
their intentions, prompt adherence, or current failure rate is not an adequate
security boundary. LeanCage aims to make the boundary an independently checkable
property of the deployed system.

## purpose: A reusable verification effort

Build a useful native-program sandbox and an extensible verification chain in
Lean 4. Start with small, reviewable parts of an existing implementation, while
keeping the connection to production Linux explicit at every step. Early model
proofs are valuable only when their remaining implementation and platform
obligations stay visible.

## scope: The destination

The destination is end-to-end correctness and isolation for named deployment
profiles, including relevant Linux enforcement and software-observable hardware
channels. It is not a claim about every Linux subsystem or every possible
machine. Each useful milestone must contribute contracts, proofs, implementation,
or evidence that the next one can extend.
