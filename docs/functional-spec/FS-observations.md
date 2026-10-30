# FS-observations: State exactly what an attacker may observe

To meet [§GOAL-confidentiality](../goals.md#goal-confidentiality-account-for-software-observable-leakage), every confidentiality claim must identify protected
information, public inputs, authorized disclosures, attacker capabilities, and the
observation function for execution traces.

## logical: Functional observations

Define equivalence of initial states and allowed differences in outputs, errors,
termination, and interaction. State whether termination is observable. Prove the
chosen noninterference or explicit leakage property rather than assuming that
access control implies confidentiality. Authorized outputs may reveal information
and must be specified as disclosures, not hidden from the model.

## hardware: Software-observable channels

The final program includes timing, cache state, contention for shared resources,
and speculative execution. Model relevant timers, co-resident attackers, schedules,
and microarchitectural behavior for each claimed profile. Functional refinement
alone does not preserve a timing-sensitive security property.

## boundary: Profile restrictions and physical exclusions

Hardware channels remain open obligations until the model, mechanisms, and proof
are connected for a named CPU/kernel/configuration profile. Restrictions such as
dedicated resources or scheduling controls require explicit contracts and useful
workload witnesses. Do not generalize one profile's theorem to all Linux systems.
Physical probing, physical tampering, and power/EM measurements are excluded.
Fidelity of the hardware model remains an explicit foundational assumption.

## evidence: Separate kinds of evidence

Leakage experiments and adversarial tests supplement formal arguments. A passing
timing test or VM demonstration is not a proof of absence of hardware leakage.
Early milestones must report that these obligations are open.
