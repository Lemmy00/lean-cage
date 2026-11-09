# DA-metadata-handles: Make the bounded reader's descriptor lifetime executable

The entry caller needs the handle frame in [§AR-metadata.frame](../../architecture/AR-metadata.md#frame-derive-the-caller-frame-from-the-same-request-history) while satisfying [§FS-metadata.bounds](../../functional-spec/FS-metadata.md#bounds-bound-every-request-and-the-returned-prefix) and [§FS-metadata.ownership](../../functional-spec/FS-metadata.md#ownership-close-only-the-handle-opened-by-this-read).

## explicit: Use explicit open, read and close control

The pinned Lean 4.35.0 `IO.FS.withFile` definition is `Handle.mk fn mode >>= f`. Its handle closes when the last reference is dropped; it exposes no explicit `Handle.close`. Treating the old complete `readBounded` action as one trusted operation would hide application ownership, loop construction and error ordering.

The maintained bounded reader now uses a shared executable request program and a small native adapter for individual `openat`, `read` and `close` operations. It validates the open word before narrowing, rejects NUL paths, requests at most 4096 bytes and checks each returned count and actual byte-array extent before appending. The only read/close descriptor comes from that same open reply. Every returning body path issues its close, including read errors. A close error prevents success, and an earlier read error remains the reported error.

The public `readBounded` signature and one-byte-over-limit convention remain. Native errors retain their numeric code and selected operation. The narrow runtime adapter saves errno before allocating its reply. Loss during allocation or a syscall is not a returned success. Linux's valid-descriptor close contract, including release on returned I/O/interruption errors, is explicit; close is never retried against a potentially recycled descriptor number.

The application proof derives the reader's frame from the actual shared sequence and the per-operation laws. It does not assume a whole reader executor, a finalizer close, a successful syscall sequence or a filesystem snapshot.
