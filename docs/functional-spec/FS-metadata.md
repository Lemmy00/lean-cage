# FS-metadata: Bounded reads with owned file handles

Metadata reads support the entry startup checks in [§FS-entry.runtime](FS-entry.md#runtime-dedicated-entry-runtime-profile) and the workspace input limits in [§FS-workspace.policy](FS-workspace.md#policy-bounded-typed-request).

## bounds: Bound every request and the returned prefix

For a natural-number limit, the reader returns at most one byte beyond that limit. Each read requests between one and 4096 bytes. The application checks the returned count, the actual byte-array extent and the requested bound before appending bytes. Empty reads finish the prefix. Errors retain their operation and numeric error code. A path containing a NUL byte is rejected before opening it.

## ownership: Close only the handle opened by this read

The application opens one read-only handle, passes that exact handle to each read, and attempts its close before returning bytes or a read error. An open failure performs no read or close. A close failure prevents a successful result; an earlier read error remains the reported error. A returned read preserves the caller's existing handle objects and entry security state under the individual Linux open/read/close contracts.

## loss: Retain interrupted and lost executions

No operation is assumed to return successfully or promptly. Waiting, read/open/close errors, allocation failure and process loss remain possible. Process loss may occur while the private handle is open; it supplies no returned metadata result and cannot authorize admission. This contract does not claim a filesystem snapshot against concurrent modification.
