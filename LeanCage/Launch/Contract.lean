namespace LeanCage.Launch

-- §FS-filter-loading.installation.effects: Portable names for the three OS boundaries.
inductive OsCall where
  | setNoNewPrivileges
  | installFilter
  | exec
  deriving DecidableEq, Repr

-- §FS-filter-loading.installation.failure: Normalize errors before constructing an observation.
abbrev Errno := { value : UInt32 // 0 < value.toNat ∧ value.toNat ≤ 4095 }

-- §FS-filter-loading.installation.failure: A failure never promises rollback of restrictions.
inductive Failure where
  | validationRejected
  | osError (operation : OsCall) (errno : Errno)
  | interrupted (operation : OsCall)
  | cancelled
  | contractViolation (operation : OsCall)
  deriving DecidableEq, Repr

-- §FS-filter-loading.installation.states: Vocabulary only; M1.3 defines permitted transitions.
inductive Stage where
  | unvalidated
  | ready
  | privilegesRestricted
  | filterInstalled
  | executing
  | executed
  | failed (reason : Failure)
  | terminated
  deriving DecidableEq, Repr

-- §FS-filter-loading.installation.states: Effects are requests, not successful OS outcomes.
inductive Effect where
  | validate
  | setNoNewPrivileges
  | installFilter
  | exec
  deriving DecidableEq, Repr

-- §FS-filter-loading.installation.states: Exec invocation and image replacement are distinct.
inductive Event where
  | validationAccepted
  | noNewPrivilegesSet
  | filterInstalled
  | execAttempted
  | execSucceeded
  | failed (reason : Failure)
  | terminated
  deriving DecidableEq, Repr

-- §AR-core.observations: Raw public observations; a list is not a valid-execution certificate.
abbrev Trace := List Event

end LeanCage.Launch
