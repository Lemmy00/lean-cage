This package implements [§AR-compiled-reporting.connection](../../docs/architecture/AR-compiled-reporting.md#connection-carry-the-reporting-argument-across-verified-compilation). Its consumer is
`CompilerCertificate.current_assembly_reporting`: the current complete helper
and explicit logical errno runtime unit compile to the identified `Asm.program`,
whose matched descriptor-1 reporting calls preserve emitted-byte prefixes and the ordinary
Lean decoder result on success. The required runtime effects and caller relation
are explicit premises. Native TLS, Linux effects, partial-call asynchronous loss,
C frontend, assembler/linker/loader and retained GCC artifact correspondence
remain open. No original M4 ledger entry is closed.

The normal integration command reuses matching checked evidence:

```sh
./scripts/check_reporting_compiler.sh
```

When a proof input changes, rebuild only invalidated clients, audit the changed
proofs, then collect an unreviewed proposed record:

```sh
python3 verification/compiler/check.py --build
python3 verification/compiler/check.py --audit
python3 verification/compiler/check.py --collect
```

The collector does not replace `assurance/reporting-compiler.json.gz`. Acceptance
requires reviewing full statements, foundations and residual premises. The
checker rejects an altered allocation and a missing runtime root. A separate
kernel checker validates the composed proof artifacts. Matching audit and
negative-control receipts are reused.

`profile.py` creates a derived backend in `.tools/reporting/compiler-backend`.
`source.py` rechecks source reporting with the runtime root in
`.tools/reporting/compiler-source`, reusing accepted pure proofs. Concrete
certificates and untrusted candidates live in `.tools/reporting/compiler`.
`candidates.py` rebuilds the untrusted candidate tool only when needed; the
outer allocation validator supplies correctness. Its `helper-candidate.s` is
untrusted presentation output. No deployed native builder uses it.

`amendment.py` checks the archived preimages and the exact aggregate-gate
fingerprint amendment. Earlier source/connection theorem rows, foundations and
compiled proof hashes remain unchanged. Proof-audit receipts depend on the
actual proof files and tools, so this operational amendment needs no rebuild.

`FrontendCertificate` checks Clight lowering, not the C parser or preprocessor.
Allocation and code-generation results are saved separately; the final compiler
equation composes those results without replaying their computations. Read
`LICENSES.md` for the adapted compiler material's separate terms.
