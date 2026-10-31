M4 revised effect layer and Lean endpoints
=========================================

This advances [§AR-m4-native.revision](../../docs/architecture/AR-m4-native.md#revision-byte-aware-effects-and-loss-before-the-lean-bridge) under [§AR-m4-effects](../../docs/architecture/AR-m4-effects.md#ar-m4-effects-byte-aware-native-effects-and-asynchronous-loss). It does **not** complete
M4.2–M4.6. No Linux or compiler obligation has been reclassified as an assumption
merely to finish a milestone.

Run from the project root, with the existing project-local M4 research tools:

```sh
./scripts/check_m4_connection.sh
./scripts/check.sh
```

The first command runs the original maintained-source/frontend/ABI/tool gate,
then compiles all 91 Rocq modules, checks their kernel terms with `coqchk`,
queries every new theorem's full type and assumptions, checks all Lean endpoint
theorems and runs the evidence regressions. The source phase has a five-minute bound and the extended proof phase a ten-minute bound.
It performs no downloads or expectation refresh and executes no guest/OS workload.
Tools and build products stay under the existing `.tools/m4` directory.

`IO.v` defines actual CompCert memory operations for arbitrary byte reads/writes,
signed errors and an owned separate errno cell. Its proofs establish transfer
bounds, errno on failure, exact read contents, buffer/frame preservation outside
permitted writes, determinate results for equal byte-aware replies and inhabited
allocations, arbitrary two-byte short reads/errors and four-byte writes. A success
can preserve or update errno; errors include EINTR and no progress is assumed.

`Machine.v` lifts actual internal Clight steps, replaces exactly the maintained
read/write/errno external signatures and adds blocking and loss at every source
boundary. Loss during transfer retains the bytes/memory effect without returning
to C. Loss after a return remains possible. Dead states have no successor. Exact
AST equations identify the source calls and signatures; they do not establish
the complete framer/terminal-receiver simulation or whole-slice memory safety.
Unsupported external functions remain unmodeled and cannot silently return through
stock Clight. The system has separate events and **does not inherit CompCert's
compiler correctness theorems**.

`ClightSteps.v`, `WriteMemory.v` and `WriteAll.v` prove the complete local
`write_all` invocation against the actual generated program. Every finite run
emits an exact input prefix and preserves the owned buffer. A live nonterminal
state has a defined source/effect step without using loss to mask undefined
behavior. Zero return requires full transfer; minus one requires a zero or
non-EINTR reply and incomplete transfer. This is partial correctness, not a
termination guarantee. `WriteWitnesses.v` constructs bounded arbitrary input,
success, short writes, arbitrary EINTR retries, errors, waits and partial loss.
See [§AR-m4-effects.writeall](../../docs/architecture/AR-m4-effects.md#writeall-universal-source-loop-connection) and [the source-proof review](../../docs/reviews/M4-writeall.md).
Actual caller composition, child-failure reporting and private-frame decoding are now checked. Frame sending, terminal reception and the checked Lean connection remain open.

`Endpoints.lean` proves observation-trace entry origin/persistence and release
requirements, rejection of private intermediate tags by the actual final decoder,
and original lifecycle receipt order using the existing M3 definitions. The Rocq
terms are not translated into Lean. These endpoint facts do not provide the
unproved C-to-Lean connection.

`assurance/m4-connection-claims.json` records full checked types/foundations;
`assurance/m4-connection-evidence.json` binds source/tool/proof artifacts;
`assurance/m4-obligations.json` retains all sixteen original M2/M3 correspondence
entries as open. The new gate rejects statement/axiom drift, missing claims,
tampered bytes, disappearing obligations and unsupported completion claims.
`assurance/m4-writeall-baseline-claims.json` preserves the preceding 31 Rocq and
12 Lean records. The active manifest adds 95 checked source-proof declarations,
and `assurance/m4-writeall-evidence.json` binds their artifacts and review receipts.

The source helper, Lean model/theorems, dependency pins and VM evidence remain
unchanged. The original M4.1 proof types/assumptions remain unchanged. Only its
roadmap/architecture-index documentation fingerprints and the preserved decision
index are deliberately advanced when linking this additive package, with old/new
identities recorded. See `docs/reviews/M4-progress.md` for the validation record
and remaining work.

The complete decoder under [§AR-m4-decoder](../../docs/architecture/AR-m4-decoder.md#ar-m4-decoder-complete-private-frame-decoding-from-owned-bytes) is connected to the actual generated
body from arbitrary owned bytes and independent output permissions. It proves
exact return conditions, early versus late rejection mutation, all-prefix
preservation/progress, local freeing, accepted-tag executions, rejection runs,
and arbitrary waits/loss. See [the decoder review](../../docs/reviews/M4-decoder.md).

The current inventory contains 680 Rocq and 12 Lean declarations. It preserves
all 494 previous declarations and 48 previous compiled artifacts. Of the 186
added records, 113 support decoder/source composition and 73 make the historical
caller import closure explicit. The exact compatibility sources in `compat/`
repair an earlier dependence on incidental ignored build files. Every project
import must now resolve to an inventoried maintained module or the preserved
M4.1 `Slice`/`Codec` inputs. No claim count is a security score.
