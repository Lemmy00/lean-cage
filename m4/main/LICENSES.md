The new proof, audit and test sources are Apache-2.0. The complete frontend input
is the unchanged Apache-2.0 `native/leancage_m3.c`; its local includes retain their
existing notices. The decimal proof adaptation preserves the maintained sources
and changes only their module namespace and the documented identifier binding.

The complete helper also includes host glibc, Linux UAPI and GCC/CompCert runtime
headers. Their paths and byte identities are recorded from the actual preprocessed
input. Their original files and notices remain in their installed locations.
No upstream header, complete preprocessed file, generated complete-helper AST or
compiler binary is redistributed by this package; those artifacts stay in the
ignored local tooling directory. Their hashes are provenance, not relicensing.

The applicable glibc, Linux UAPI, GCC runtime and individual header licenses and
exceptions remain in force for any later redistribution. The root Apache license
does not override them. CompCert and the isolated checker retain the source pins
and research-use/licensing boundaries described in `m4/LICENSES.md` and
`m4/bridge/LICENSES.md`. This profile changes no dependency pin or installed tool.
