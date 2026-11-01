# Live launch-plan bytes and native decimal source connection

This package follows [§AR-m4-controller.plan](../architecture/AR-m4-controller.md#plan-live-lean-plan-fields-and-their-decimal-bytes) and
[§DA-m4-controller.plan](../decisions/architectural/DA-m4-controller.md#plan-normalize-the-numeric-byte-interface-preserve-the-live-encoder)
from native decimal checkpoint `c93c550ec9c0559e1421e624cd637ff570f44b73`.
It preserves the live launcher, native helper, tool pins and previous proof
artifacts. The claim review follows [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition).

The Lean layout theorems refer to the actual `LeanCageM3.planArgs`. They recover
the mode, all ten numeric fields in order, parent PID, export choice, optional
digest texts and unchanged guest-argument suffix. The pure `nativeArgs` operation
prepends an executable name and proves the resulting native-facing positions and
17–80 argument bound for a policy whose actual `argvValid` predicate succeeds.
This does not prove that `IO.Process.spawn` or Linux creates that argument table.
Digest text extraction is exact; digest validity is not inferred for an arbitrary
constructed `Policy`.

`decimal_utf8` identifies the actual `toString`/UTF-8 bytes with the ASCII codes of
the standard decimal digits. The proofs establish the exact mathematical value,
nonempty representation, absence of NUL, and a twenty-byte bound for unsigned
64-bit values. `numeric_fields_decoded` applies the byte parser to the actual ten
encoded limit fields. `limitsValid` entails that each fits the unsigned range;
the fixed CPU period is proved separately and is not silently inserted into the
serialized list. Every UInt32 parent PID fits the decimal parser, but positivity,
signed-PID range and `getppid` agreement remain controller/kernel obligations.

`parseDecimal` is a proof-side byte interface, not an additional deployed parser.
`parse_decimal_exact` characterizes its complete language for an arbitrary bound.
It rejects empty input, non-digits and overflow and accepts leading zeros. The
strictly imported computational root is this definition itself. Its closure has
173 declaration entries, including no exported axiom and no unsupported string,
character or UInt32 closure. The existing importer and its settings are retained.

`plan_fold_exact`, `plan_digits_exact` and `plan_parser_exact` give the imported
terms' exact ordinary arithmetic/list meaning. `plan_parser_some`,
`plan_parser_none` and `plan_parser_value` connect all outcomes to the previously
proved actual C `number` routine. They quantify over arbitrary source bytes;
neither acceptance nor an execution is assumed. The supplied bound at this
connection is exactly UINT64_MAX.

`plan_source_path` and `plan_source_execution` construct complete actual source
runs from independently owned input and output memory, using the imported result
for both return code and final store. The return, prefix, progress, loss,
rejection-memory and successful-value theorems preserve the corresponding native
guarantees. Arbitrary caller continuations remain in the constructive paths;
all-run claims use a stopped caller. Output/input overlap is retained. The same
sequential-source and deployed-store-atomicity limitations as the decimal
checkpoint apply.

The byte interface rejects a logical list containing NUL. The C routine instead
stops at its first NUL; its input-ownership premise describes exactly the prefix
before that terminator. No source theorem claims to reject bytes following it.
The live decimal encoder's absence-of-NUL theorem supplies the relevant shape
fact, while actual memory ownership remains a runtime/controller obligation.

Allocated separate and overlapping source witnesses connect the imported parser
to all twenty preceding cases, ten accepted and ten rejected. These are forty
constructed source realizations, not fresh native measurements. Lean witnesses
also include ordinary and preflight plans, accepted decimal boundaries, malformed
bytes, overflow and invalid policy examples. All use ordinary kernel checking.

The audit inventories 32 authored Rocq theorems and 88 Lean theorem records
(46 authored statements plus generated auxiliaries/equations). Twelve Rocq records
report no axioms or definitional UIP; one uses the imported equality's definitional
UIP; eight use the four imported logical instances; eleven additionally retain
the six existing source-semantics/logical foundations. The imported endpoint uses
the same four instances: `eq`, `eq_inst1`, `True` and `HEq_inst1`. Lean's transitive
foundation union is `propext`, `Quot.sound` and `Classical.choice`. No foundation is
hidden or replaced with an unchecked evaluation shortcut.

`python3 m4/plan/check.py` is the maintained gate. It records full types and
foundations, seven compiled identities, exact export bytes, ten integrity
regressions, refusal of disabled guardedness, and independent kernel replay.
The evidence preserves the 83-record native checkpoint, 135/33-record frame
checkpoint, all previous compiled identities and archived receipts. Parent
replays and repository checks are recorded in `assurance/m4-plan-evidence.json`.

This is a checked endpoint/source connection under an explicit representation
premise. Translation faithfulness, the importer's logical-model review, actual
argument provenance and memory ownership, the native main routine's sequential
stores and later failure ordering, and all sixteen original native/Linux ledger
obligations remain open. It does not complete M4.2, M4.3, the executable/runtime
chain, Linux enforcement or hardware confidentiality.
