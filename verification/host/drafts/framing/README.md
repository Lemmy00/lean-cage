# Response framing draft

This historical draft is superseded by the checked `GatewayFraming`,
`GatewaySourceFraming`, `GatewayResponseFraming` and `GatewayDecodedFraming`
modules. `assurance/host-framing-review.json` records their full statements,
assumptions, actual parser-result consumer and the still-required physical prefix
producer. Preserve these old draft bytes and diagnostics; do not resume them.

Preserved at the user-requested M5.2 pause. These text files are unfinished proof
work, excluded from maintained Rocq module discovery and all accepted claims.
They neither change the executable codec nor supply the response provenance
connection required by [§FS-host-boundary.acceptance](../../../../docs/functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation).

The next action is to finish `GatewayCanonicalBytes.gateway_plain_tag_encoding`:
normalize the one-byte fold in its actual `VALUE` hypothesis and establish the
singleton result. Then check the canonical-subject induction interface and prove
prefix uniqueness for the unchanged imported `SourceEncoded` relation, restricting
scalar tags to 3, 4, 5, 6 and 9. The parser's actual heap semantics and maintained
writer view must produce that restriction; it cannot be added as an unexplained
application premise. Preserve the SProp/Prop distinction and existing axiom gate.

No complete framing uniqueness theorem has been written or checked. The latest
focused failures and exact draft bytes are retained beside this note.
