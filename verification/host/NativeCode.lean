namespace LeanCage.Host.NativeCode

-- §AR-host-boundary.primitives: This separate strict data boundary contains only Nat/Bool/lists.
-- Decoding validates every byte and machine word before constructing the ordinary operation.
structure Request where
  op : Nat
  first : Nat
  second : Nat
  third : Nat
  left : List Nat
  right : List Nat

inductive VfsOperation where
  | adapted (request : Request)
  | linkAt (sourceDirectory : Nat) (source : List Nat)
      (targetDirectory : Nat) (target : List Nat) (flags : Nat)
  | symlinkAt (contents : List Nat) (directory : Nat) (name : List Nat)
  | renameAt (sourceDirectory : Nat) (source : List Nat)
      (targetDirectory : Nat) (target : List Nat) (flags : Nat)
  | chdir (path : List Nat)
  | fchdir (fd : Nat)
  | fchmod (fd mode : Nat)
  | fchown (fd owner group : Nat)
  | truncate (fd extent : Nat)
  | seek (fd offset whence : Nat)
  | pwrite (fd : Nat) (bytes : List Nat) (extent offset : Nat)
  | setInodeFlags (fd flags : Nat)
  | setEncryptionPolicy (fd : Nat) (policy : List Nat)
  | setAttribute (fd : Nat) (name value : List Nat) (flags : Nat)
  | removeAttribute (fd : Nat) (name : List Nat)
  | fchmodAt (directory : Nat) (path : List Nat) (mode flags : Nat)
  | fchownAt (directory : Nat) (path : List Nat) (owner group flags : Nat)

inductive FileAction where
  | close (fd : Nat)
  | duplicate (source target : Nat)
  | closeFrom (minimum : Nat)
  | open (fd : Nat) (path : List Nat) (flags mode : Nat)
  | chdir (path : List Nat)
  | fchdir (fd : Nat)

structure SpawnAttributes where
  flags : Nat
  processGroup : Nat
  signalMask : List Nat
  signalDefault : List Nat
  schedulingPolicy : Nat
  schedulingPriority : Nat

structure Spawn where
  path : List Nat
  arguments : List (List Nat)
  environment : List (List Nat)
  actions : List FileAction
  attributes : SpawnAttributes

structure Exec where
  path : List Nat
  arguments : List (List Nat)
  environment : List (List Nat)

structure PollEntry where
  descriptor : Nat
  events : Nat

inductive Operation where
  | vfs (operation : VfsOperation)
  | socketPair (domain socketType protocol : Nat)
  | fcntl (fd command argument : Nat)
  | duplicate (source target flags : Nat)
  | send (fd : Nat) (bytes : List Nat) (extent flags : Nat)
  | receive (fd extent flags : Nat)
  | shutdown (fd how : Nat)
  | poll (entries : List PollEntry) (timeout : Nat)
  | clock (clockId : Nat)
  | signal (pid signal : Nat)
  | waitPid (pid options : Nat)
  | spawn (arguments : Spawn)
  | exec (arguments : Exec)

structure Reply where
  word : Nat
  bytes : List Nat

-- §FS-host-boundary.ownership: Committed products are independent of returned/error/lost replies.
inductive Product where
  | none
  | socketPair (first second : Nat)
  | sent (bytes : List Nat)
  | received (bytes : List Nat)
  | created (child : Nat)
  | executed (image : Nat)
  | reaped (child : Nat) (status : Nat)

structure Handle where
  object : Nat
  description : Nat
  flags : Nat
  rawOwned : Bool

structure References where
  handles : Nat → Option Handle
  closeOnExec : Nat → Bool
  workingDirectory : Nat

structure Credentials where
  uid : Nat
  groups : List Nat
  bypassDac : Bool
  bypassOwner : Bool

-- §AR-host-boundary.interfaces.gateway: Source invocation and all primitive fields share one row.
structure SourceKey where
  process : Nat
  entryPosition : Nat
  actionsLifetime : Nat
  attributesLifetime : Nat

structure CallRow where
  process : Nat
  caller : Credentials
  beforeReferences : References
  afterReferences : References
  operation : Operation
  reply : Option Reply
  product : Product

end LeanCage.Host.NativeCode
