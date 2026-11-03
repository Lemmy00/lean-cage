# Early connection feasibility replay

This inspection package implements [§AR-m4-routes.evidence](../../docs/architecture/AR-m4-routes.md#evidence-replay-and-claim-boundary).
It records failed connections and their replacement routes, not security results.

Prepare the existing M4 bridge and M3 VM **build inputs** using their documented
procedures. No fresh VM run is required. Prepare the separate inspection checkout:

```sh
python3 m4/routes/check.py --prepare
python3 m4/routes/check.py
```

The inspection revision is Certora/clean
`123f7f7767e215aceb4821f0d044336d78103ade`. Its sources remain in
`.tools/m4/proof-connection/clean`, with the original upstream license. They are
not a maintained dependency. The experiment overrides its Lean version on the
command line with this project's existing Lean 4.35 pin and changes no pin.
CompCert's upstream licensing continues to apply to that checkout and its
serialized computational closure; the project's Apache license does not replace
it. No upstream source or closure is vendored by this package.

The gate builds the actual port, audits `CC.doStep_sound`, exports actual
`CC.Step`, and checks two strict import failures at its nested `CC.Ty` recursor.
It also preprocesses the unchanged configured kernel pipe translation unit and
checks the maintained frontend's rejection of `__int128`. All outputs go to
`.tools/m4/routes`; there is no kernel/guest execution or host reconfiguration.

`--collect` writes only an ignored report. Normal replay compares reviewed input,
audit and failure records. Kernel-source semantics, the read-fault producer,
semantics equivalence, compiler/runtime composition and full M4 remain open.
