# Complete digest recognizer: claim review

This package follows [§AR-m4-controller.digest](../architecture/AR-m4-controller.md#digest-actual-lowercase-digest-text-validation) and [§DA-m4-controller.digest](../decisions/architectural/DA-m4-controller.md#digest-reuse-owned-strings-for-the-actual-digest-recognizer) from
argument checkpoint `90461f618929b6734bec22c6c43fbe47ee687b0b`. It connects the
unchanged complete-helper `digest_text` function to an exact lowercase hexadecimal
byte predicate and the actual live Lean digest-field parser. This review applies
[§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition) to the complete propositions and their transitive
foundations. All earlier source, header, tool, theorem and compiled identities
remain preserved.

`digest_source` assumes only an independently owned initialized C string, an
arbitrary effect-cell parameter and caller continuation. It constructs a real
entry-to-return path in the existing conservative string machine. The return is
one exactly for sixty-four bytes, each in ASCII 0–9 or a–f, and zero otherwise.
No validity, successful-execution or desired-return premise is assumed. The
complete helper's frontend output supplies the function body; structure and
length-condition identities are checked against it.

The source calls `strlen` before examining characters. Wrong-length input returns
immediately. At length sixty-four, the proof follows the actual unsigned index,
signed `Mint8signed` loads, repeated reads and short-circuit conditions. The
signed-byte interpretation is proved from sign extension and byte bounds. Every
high-bit byte rejects. Pointer arithmetic and all reads derive from the owned
string, including its nonwrapping span; the source never writes memory. The
loop stops at its first rejected character. No content-authentication or SHA-256
claim follows from recognizing its textual spelling.

The constructed path takes at most 2,068 non-wait steps, including the local
`strlen` return. `StringControl` converts these paths into whole-function
certificates. For an isolated call with `Kstop`, every actual execution preserves
all memory and has at most 2,069 non-wait events, allowing loss after return.
Every live prefix either has the exact final return or has defined ordinary
progress. Every completed return equals the exact byte predicate. These
universal results have no assumed prefix-length bound. Constructive paths retain
arbitrary caller continuations; the all-execution theorem stops at an isolated
return so it does not attribute later caller behavior to this function.

The machine keeps all preceding library/source transitions, arbitrary waiting
at `strlen`, and asynchronous loss. Every path boundary has an interruption
witness, and the actual first library call is reached through four source steps
before arbitrary waiting and loss. No wall-clock bound, survival or unconditional
termination is claimed. The sequential model has no interfering memory-writer
transition; a whole-controller justification of that premise remains open.

Nonvacuity starts with constructible initial memory for the actual complete
program. Eighteen allocated cases include five accepted strings and thirteen
rejections: all four ASCII range endpoints, mixed digits/letters, empty and
63/65-byte strings, uppercase, neighboring invalid characters, high bytes,
whitespace, and first/last-position failures. Each has actual source, wait and
every-prefix loss witnesses. Two further allocations include bytes after the
first NUL: a 32-byte prefix rejects and a 64-byte prefix accepts, despite trailing
invalid bytes. They establish the C-string boundary rather than incorrectly
treating an interior NUL as part of an owned string.

The exact computational Lean interface contains recursive byte count and
lowercase-hex predicates. Its 149-entry export has no exported axiom and passes
the unchanged strict importer. Rocq interprets the actual imported terms and
proves agreement with the native predicate, constructed source paths and every
completed return. A constructive encoding represents every byte list in the
imported list type, so the representation premise is inhabited. Allocated
source witnesses also reach the imported result.

Ordinary Lean proofs connect accepted digest text to exactly sixty-four UTF-8
bytes and absence of NUL. `live_digest_equation` is a definitional identity for
the existing private `digestField`; a name-only macro references that declaration
without changing the live module. The successful-`some` theorem follows its
actual field lookup, null branch, string conversion and rejection condition.
It establishes the `sha256:` prefix and valid stripped suffix. The two plan
theorems place that suffix at native positions fourteen and fifteen, conditional
on the corresponding policy field being that parsed value. They do not assume
or establish the complete JSON parser, Linux argument storage or the native
caller's `none` alternative.

The gate records 86 Rocq and 193 Lean full theorem records plus the imported
endpoint. The Lean inventory includes generated equations and library helpers
created while checking the closed parser examples; it is not a count of authored
security claims. Full printing includes proof arguments that the default printer
abbreviates. Lean foundations are limited to the previously reviewed `propext`,
`Classical.choice` and `Quot.sound`: 121 records have none, 51 use all three,
thirteen use `propext` and `Quot.sound`, seven use `propext`, and one uses only
`Quot.sound`. The checked `cbv` examples introduce no compiler-trust axiom.

Of the 86 Rocq records, 31 have no foundations, 34 use the existing six logical
and external-semantics entries, twelve use the existing four logical entries,
five use only the four reviewed definitional-UIP instances, and four use both
the six entries and those instances. The imported endpoint also uses those four
UIP instances. The full types and exact transitive names are saved with the
compiled identities; translation faithfulness and logical-model review remain
explicit obligations.

`python3 m4/digest/check.py` replays sixteen compiled identities, the strict
export/import, independent kernel checking, twelve integrity regressions and
three compiled negative checks: disabled import guards, a 64-to-63 native length
identity mutation, and a 64-to-63 live parser mutation. The latter has a positive
control and exposes the concrete mismatch on a valid 64-byte digest: the altered
body rejects while the actual parser accepts. The preserved argument checkpoint is immutable; active
older manifests receive only named documentation and transitive fingerprint
amendments. Earlier propositions, artifacts, pins and raw receipts remain
unchanged.

All sixteen original obligations remain open. Whole-main entry, the parent's
identity, native digest/export/allowlist caller checks, reporting after rejection,
setup/supervision/cleanup, libc and Linux effects, compiler/runtime/linker/loader
correspondence, independent composed review and hardware channels remain
unfinished. This advances M4.3; it does not complete M4.
