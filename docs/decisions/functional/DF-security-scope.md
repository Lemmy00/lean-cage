# DF-security-scope: Include software-observable hardware channels in the destination

**Status: accepted.** The endpoint includes arbitrary malicious native workloads,
the relevant Linux enforcement environment, and software-observable hardware
channels under [§FS-isolation](../../functional-spec/FS-isolation.md#fs-isolation-confine-all-supported-guest-effects) and [§FS-observations](../../functional-spec/FS-observations.md#fs-observations-state-exactly-what-an-attacker-may-observe), following [§GOAL-end-to-end](../../goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact).

## scope: Exact promises

Include timing, caches, contention, and speculative execution for named profiles.
Exclude physical tampering and physical power/EM measurements. The objective is
an expanding set of useful production profiles, not a theorem about all of Linux
or every possible device.

## staging: Make smaller claims while preserving the endpoint

M1–M3 may assume kernel enforcement and omit hardware secrecy claims, provided the
assumption register reports these gaps. M4 and M5 must address them explicitly.
The difficulty of these research milestones is not a reason to quietly rename
an early model proof as end-to-end verification.
