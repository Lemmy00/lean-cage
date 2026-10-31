M4.1 native-semantics feasibility
===============================

The result is mixed: the real pure byte readers have checked Clight executions;
the attempted direct silent/count-only effect adapter is refuted. Full reporting
simulation and whole-slice memory safety are unfinished, and no Lean bridge exists.
See [§AR-m4-native.outcome](../docs/architecture/AR-m4-native.md#outcome-checked-pure-core-and-rejected-direct-effect-adapter) and [§AR-m4-native.revision](../docs/architecture/AR-m4-native.md#revision-byte-aware-effects-and-loss-before-the-lean-bridge) for the exact limits and revised
route. This is a bounded feasibility result, not a completed native security proof.

Replay on the recorded Ubuntu 24.04 x86-64 tool/header profile:

```sh
# Read m4/LICENSES.md before the first research-tool bootstrap.
python3 m4/bootstrap.py
./scripts/check_m4.sh
./scripts/check.sh
```

Bootstrap verifies package/archive pins and extracts/builds only in `.tools/m4`;
it does not install packages, change global settings or execute maintainer scripts.
The assigned CompCert commit reports 3.17, despite the inherited 3.18 label.
Coq 8.18.0 is the compatible prover (before its Rocq rename), OCaml 4.14.1 and
Menhir 20231231 are pinned separately. Two build jobs keep host load bounded.
Bootstrap supports exactly the recorded profile; it uses the existing host GCC,
libc, GMP, standard system build tools and headers, whose relevant identities are
recorded. It is not a hermetic toolchain or compiler verification.

The normal gate has a five-minute outer bound and per-command deadlines; it has
no downloads, no expectation-refresh mode and no VM/guest execution. It verifies
all 570 upstream archive files, pinned packages and extracted package contents,
licenses, generated source/preprocessor/AST identities, full Rocq theorem and Lean
target types/assumptions, then recompiles and runs `coqchk` plus in-memory/ABI tests.
The recorded frontend executable is a local research build, identified separately.
A changed compiler/header/tool profile needs a deliberate evidence review.

`extract.py` selects maintained C function definitions and the terminal-receiver
excerpt, changing whitespace only. ABI typedefs/macros, wrapper inputs and the
function-address roots are explicit experiment adapters. The frontend command is
run inside `.tools/m4/input` so generated paths are relative:

```sh
../CompCert/clightgen -normalize -fstruct-passing -dprepro -o Slice.v slice.c
```

The complete C input is 260 conventional authored lines (218 in the extraction and 42 in its ABI header), including adapters. The generated
AST and preprocessed input are archived in assurance, and regenerated/compared on
each gate run. The original helper is never compiled into a host workload. The
witness harness substitutes memory-only read/write/close/errno/exit effects; loss
is represented by escaping the harness, not by killing a real helper process.

`Codec.v` proves actual AST body, call and small-step results for arbitrary readable
4/8-byte inputs; read-only memory and nonvacuity are explicit. `Effects.v` contains
the adapter refutations and a separate unconnected effect model. `Attempt.v`
retains the first unresolved native-effect obligation with `Abort`, exports no
proof for it, and proves that the obligation belongs to the actual AST call.
Ordinary `vm_compute` reductions in proofs produce kernel-checked terms; there
is no native-compute/compiler-trust proof shortcut.

Rocq's reported dependencies include classical logic, dependent functional
extensionality, two constructive-real decision principles, and (for semantic
propositions) external/inline-assembly semantics parameters. These are audited
verbatim per declaration. They are **not** Lean's three logical foundations and
have not been translated into Lean. The pure proofs do not use a syscall-success
axiom. Existing Lean targets are queried live and retain their audited axiom sets.

Read `docs/reviews/M4.1-handoff.md` and the additive `assurance/m4-*` ledger for
commands, hashes, proved/unproved edges and the route decision. All baseline
files except the roadmap and architecture index are frozen by the M4 evidence gate; M1/M2/M3 statement,
manifest, toolchain, native/filter, profile and VM evidence bytes remain intact.

The generated AST (`assurance/m4-slice.v.gz`) and complete Coq command output
(`assurance/m4-proof-output.log.gz`) are stored with deterministic gzip compression
to retain the frontend/printer bytes exactly, including trailing whitespace. The
gate checks both compressed and uncompressed hashes. Use `gzip -dc` to inspect.
