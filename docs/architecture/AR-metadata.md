# AR-metadata: Execute bounded metadata control over individual operations

The shared executable metadata program implements [§FS-metadata.bounds](../functional-spec/FS-metadata.md#bounds-bound-every-request-and-the-returned-prefix), [§FS-metadata.ownership](../functional-spec/FS-metadata.md#ownership-close-only-the-handle-opened-by-this-read) and [§FS-metadata.loss](../functional-spec/FS-metadata.md#loss-retain-interrupted-and-lost-executions).

## control: Share the open, bounded loop and close sequence

`LeanCageM3.Metadata` owns the request program, reply validation, bounded loop and close sequence. The public `readBounded` wrapper and the entry worker interpret this same program. Loop fuel is the natural-number limit plus one; each continued iteration has appended a nonempty checked chunk. A caller cannot supply a handle to the program: the read and close handle is decoded from its own successful open reply.

## primitives: Keep the Linux and runtime boundary narrow

The explicit lifetime choice is recorded in [§DA-metadata-handles.explicit](../decisions/architectural/DA-metadata-handles.md#explicit-use-explicit-open-read-and-close-control).

The native adapter dispatches exactly one named `openat`, `read` or `close` operation. It preserves the actual returned count/error and copied bytes. Open uses read-only and close-on-exec flags. The read buffer and the application request are bounded by 4096 bytes. Native descriptor and count narrowing uses the explicit Linux x86-64 widths. Runtime allocation failure is loss, including when a syscall has already changed the private handle or offset.

The read adapter initializes its fixed buffer and copies at most the requested
extent. An impossible positive return retains its raw word with an empty byte
array, so the shared program rejects the mismatch before appending. This bound
also applies to an intercepted return outside the protected caller context.

| Tag | Native arguments | Returned storage |
|---|---|---|
| 0 | `openat(AT_FDCWD,path,O_RDONLY|O_CLOEXEC,0)` | Borrowed NUL-terminated Lean string; no output bytes |
| 1 | `read((int)fd,buffer,(size_t)amount)` | Owned initialized 4096-byte stack buffer; actual validated prefix copied into the Lean byte array |
| 2 | `close((int)fd)` | No output bytes; descriptor is checked against `INT_MAX` before narrowing |

The foreign result is the raw `BaseIO` pair of a boxed unsigned 64-bit word and
an owned byte array. Negative results encode the captured errno in two's
complement, with EIO for an invalid errno; capture precedes all Lean allocation.
The ABI asserts 64-bit pointers, long and size_t and 32-bit native descriptors.
Application proofs establish each requested amount and descriptor bound; the
adapter also checks them before invoking read or close.

The open contract supplies a previously unused descriptor slot; it does not assume a distinct underlying inode. Read preserves the descriptor table and entry state. Linux close releases the valid owned descriptor on return, including its reported I/O/interruption errors. The application proves that the closed descriptor is still its own open result. Compiler/runtime/FFI and these individual Linux laws remain in the platform boundary; no whole reader frame or successful reader executor is a primitive premise.

## frame: Derive the caller frame from the same request history

The verification adapter interprets the shared program's actual open/read/close requests. Successful open adds one fresh slot. Reads retain its ownership. The selected close removes precisely that slot. Consequently a returned metadata read restores the caller's descriptor table and preserves the remaining entry state, including an initially empty filter list. Failure and loss prefixes remain explicit; a failed startup inspection cannot produce an admission path.

`MetadataOriginContract` retains foreign tracer contexts and intercepted return
origins. The source-derived caller snapshot and clean task lineage establish
genuine kernel origins separately at each metadata operation. Only then does
`bounded_metadata_from_caller` derive the complete reader frame. The shared
startup completes both inspections before admission begins; its stateful
execution supplies the ordinary control and native effect traces from the same
post-worker-exec state.
