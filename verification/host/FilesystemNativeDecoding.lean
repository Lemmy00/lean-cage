import NativeCode
import FilesystemNativeOperations

namespace LeanCage.Host.NativeCode

-- §AR-host-boundary.primitives: Out-of-range source words/bytes reject before narrowing.
def word? (value : Nat) : Option UInt64 :=
  if value < 2 ^ 64 then some (UInt64.ofNat value) else none

def byte? (value : Nat) : Option UInt8 :=
  if value < 256 then some (UInt8.ofNat value) else none

def list? {α β : Type} (read : α → Option β) : List α → Option (List β)
  | [] => some []
  | head :: tail => do
    let first ← read head
    let rest ← list? read tail
    return first :: rest

def encodeBytes (value : ByteArray) : List Nat := value.data.toList.map UInt8.toNat

def bytes? (values : List Nat) : Option ByteArray := do
  let bytes ← list? byte? values
  return ⟨bytes.toArray⟩

def op? : Nat → Option Filesystem.Op
  | 0 => some .openAt
  | 1 => some .read
  | 2 => some .write
  | 3 => some .close
  | 4 => some .stat
  | 5 => some .mkdirAt
  | 6 => some .renameNew
  | 7 => some .unlinkAt
  | 8 => some .random
  | 9 => some .dirOpen
  | 10 => some .dirNext
  | 11 => some .dirClose
  | 12 => some .sha256
  | 13 => some .clock
  | 14 => some .temporary
  | 15 => some .euid
  | 16 => some .socket
  | 17 => some .connect
  | 18 => some .poll
  | 19 => some .socketError
  | 20 => some .setAttribute
  | 21 => some .getAttribute
  | 22 => some .workingDirectory
  | 23 => some .signal
  | 24 => some .authenticate
  | 25 => some .equalSecret
  | 26 => some .closeOnExec
  | 27 => some .directoryIdentity
  | 28 => some .selfExecutable
  | 29 => some .filesystemType
  | 30 => some .inodeFlags
  | _ => none

def encodeRequest (value : Filesystem.Request) : Request :=
  ⟨value.op.code.toNat, value.first.toNat, value.second.toNat, value.third.toNat, encodeBytes value.left, encodeBytes value.right⟩

def request? (value : Request) : Option Filesystem.Request := do
  let op ← op? value.op
  let first ← word? value.first
  let second ← word? value.second
  let third ← word? value.third
  let left ← bytes? value.left
  let right ← bytes? value.right
  return ⟨op, first, second, third, left, right⟩

def encodeVfs : Kernel.NativeVfsOperation → VfsOperation
  | .adapted request => .adapted (encodeRequest request)
  | .linkAt sourceDirectory source targetDirectory target flags => .linkAt (sourceDirectory.toNat) (encodeBytes source) (targetDirectory.toNat) (encodeBytes target) (flags.toNat)
  | .symlinkAt contents directory name => .symlinkAt (encodeBytes contents) (directory.toNat) (encodeBytes name)
  | .renameAt sourceDirectory source targetDirectory target flags => .renameAt (sourceDirectory.toNat) (encodeBytes source) (targetDirectory.toNat) (encodeBytes target) (flags.toNat)
  | .chdir path => .chdir (encodeBytes path)
  | .fchdir fd => .fchdir (fd.toNat)
  | .fchmod fd mode => .fchmod (fd.toNat) (mode.toNat)
  | .fchown fd owner group => .fchown (fd.toNat) (owner.toNat) (group.toNat)
  | .truncate fd extent => .truncate (fd.toNat) (extent.toNat)
  | .seek fd offset whence => .seek (fd.toNat) (offset.toNat) (whence.toNat)
  | .pwrite fd bytes extent offset => .pwrite (fd.toNat) (encodeBytes bytes) (extent.toNat) (offset.toNat)
  | .setInodeFlags fd flags => .setInodeFlags (fd.toNat) (flags.toNat)
  | .setEncryptionPolicy fd policy => .setEncryptionPolicy fd.toNat (encodeBytes policy)
  | .setAttribute fd name value flags => .setAttribute (fd.toNat) (encodeBytes name) (encodeBytes value) (flags.toNat)
  | .removeAttribute fd name => .removeAttribute (fd.toNat) (encodeBytes name)
  | .fchmodAt directory path mode flags => .fchmodAt directory.toNat (encodeBytes path) mode.toNat flags.toNat
  | .fchownAt directory path owner group flags =>
      .fchownAt directory.toNat (encodeBytes path) owner.toNat group.toNat flags.toNat

def vfs? : VfsOperation → Option Kernel.NativeVfsOperation
  | .adapted request => do
    let decoded_request ← request? request
    return .adapted decoded_request
  | .linkAt sourceDirectory source targetDirectory target flags => do
    let decoded_sourceDirectory ← word? sourceDirectory
    let decoded_source ← bytes? source
    let decoded_targetDirectory ← word? targetDirectory
    let decoded_target ← bytes? target
    let decoded_flags ← word? flags
    return .linkAt decoded_sourceDirectory decoded_source decoded_targetDirectory decoded_target decoded_flags
  | .symlinkAt contents directory name => do
    let decoded_contents ← bytes? contents
    let decoded_directory ← word? directory
    let decoded_name ← bytes? name
    return .symlinkAt decoded_contents decoded_directory decoded_name
  | .renameAt sourceDirectory source targetDirectory target flags => do
    let decoded_sourceDirectory ← word? sourceDirectory
    let decoded_source ← bytes? source
    let decoded_targetDirectory ← word? targetDirectory
    let decoded_target ← bytes? target
    let decoded_flags ← word? flags
    return .renameAt decoded_sourceDirectory decoded_source decoded_targetDirectory decoded_target decoded_flags
  | .chdir path => do
    let decoded_path ← bytes? path
    return .chdir decoded_path
  | .fchdir fd => do
    let decoded_fd ← word? fd
    return .fchdir decoded_fd
  | .fchmod fd mode => do
    let decoded_fd ← word? fd
    let decoded_mode ← word? mode
    return .fchmod decoded_fd decoded_mode
  | .fchown fd owner group => do
    let decoded_fd ← word? fd
    let decoded_owner ← word? owner
    let decoded_group ← word? group
    return .fchown decoded_fd decoded_owner decoded_group
  | .truncate fd extent => do
    let decoded_fd ← word? fd
    let decoded_extent ← word? extent
    return .truncate decoded_fd decoded_extent
  | .seek fd offset whence => do
    let decoded_fd ← word? fd
    let decoded_offset ← word? offset
    let decoded_whence ← word? whence
    return .seek decoded_fd decoded_offset decoded_whence
  | .pwrite fd bytes extent offset => do
    let decoded_fd ← word? fd
    let decoded_bytes ← bytes? bytes
    let decoded_extent ← word? extent
    let decoded_offset ← word? offset
    return .pwrite decoded_fd decoded_bytes decoded_extent decoded_offset
  | .setInodeFlags fd flags => do
    let decoded_fd ← word? fd
    let decoded_flags ← word? flags
    return .setInodeFlags decoded_fd decoded_flags
  | .setEncryptionPolicy fd policy => do
    let decoded_fd ← word? fd
    let decoded_policy ← bytes? policy
    return .setEncryptionPolicy decoded_fd decoded_policy
  | .setAttribute fd name value flags => do
    let decoded_fd ← word? fd
    let decoded_name ← bytes? name
    let decoded_value ← bytes? value
    let decoded_flags ← word? flags
    return .setAttribute decoded_fd decoded_name decoded_value decoded_flags
  | .removeAttribute fd name => do
    let decoded_fd ← word? fd
    let decoded_name ← bytes? name
    return .removeAttribute decoded_fd decoded_name
  | .fchmodAt directory path mode flags => do
    let decoded_directory ← word? directory
    let decoded_path ← bytes? path
    let decoded_mode ← word? mode
    let decoded_flags ← word? flags
    return .fchmodAt decoded_directory decoded_path decoded_mode decoded_flags
  | .fchownAt directory path owner group flags => do
    let decoded_directory ← word? directory
    let decoded_path ← bytes? path
    let decoded_owner ← word? owner
    let decoded_group ← word? group
    let decoded_flags ← word? flags
    return .fchownAt decoded_directory decoded_path decoded_owner decoded_group decoded_flags

def encodeAction : Kernel.NativeFileAction → FileAction
  | .close fd => .close (fd.toNat)
  | .duplicate source target => .duplicate (source.toNat) (target.toNat)
  | .closeFrom minimum => .closeFrom (minimum.toNat)
  | .open fd path flags mode => .open (fd.toNat) (encodeBytes path) (flags.toNat) (mode.toNat)
  | .chdir path => .chdir (encodeBytes path)
  | .fchdir fd => .fchdir (fd.toNat)

def action? : FileAction → Option Kernel.NativeFileAction
  | .close fd => do
    let decoded_fd ← word? fd
    return .close decoded_fd
  | .duplicate source target => do
    let decoded_source ← word? source
    let decoded_target ← word? target
    return .duplicate decoded_source decoded_target
  | .closeFrom minimum => do
    let decoded_minimum ← word? minimum
    return .closeFrom decoded_minimum
  | .open fd path flags mode => do
    let decoded_fd ← word? fd
    let decoded_path ← bytes? path
    let decoded_flags ← word? flags
    let decoded_mode ← word? mode
    return .open decoded_fd decoded_path decoded_flags decoded_mode
  | .chdir path => do
    let decoded_path ← bytes? path
    return .chdir decoded_path
  | .fchdir fd => do
    let decoded_fd ← word? fd
    return .fchdir decoded_fd

def encodeAttributes (value : Kernel.NativeSpawnAttributes) : SpawnAttributes :=
  ⟨value.flags.toNat, value.processGroup.toNat, value.signalMask, value.signalDefault, value.schedulingPolicy.toNat, value.schedulingPriority.toNat⟩

def attributes? (value : SpawnAttributes) : Option Kernel.NativeSpawnAttributes := do
  let flags ← word? value.flags
  let processGroup ← word? value.processGroup
  let schedulingPolicy ← word? value.schedulingPolicy
  let schedulingPriority ← word? value.schedulingPriority
  return ⟨flags, processGroup, value.signalMask, value.signalDefault, schedulingPolicy, schedulingPriority⟩

def encodeSpawn (value : Kernel.NativeSpawn) : Spawn :=
  ⟨encodeBytes value.path, value.arguments.map encodeBytes, value.environment.map encodeBytes, value.actions.map encodeAction, encodeAttributes value.attributes⟩

def spawn? (value : Spawn) : Option Kernel.NativeSpawn := do
  let path ← bytes? value.path
  let arguments ← list? bytes? value.arguments
  let environment ← list? bytes? value.environment
  let actions ← list? action? value.actions
  let attributes ← attributes? value.attributes
  return ⟨path, arguments, environment, actions, attributes⟩

def encodeExec (value : Kernel.NativeExec) : Exec :=
  ⟨encodeBytes value.path, value.arguments.map encodeBytes, value.environment.map encodeBytes⟩

def exec? (value : Exec) : Option Kernel.NativeExec := do
  let path ← bytes? value.path
  let arguments ← list? bytes? value.arguments
  let environment ← list? bytes? value.environment
  return ⟨path, arguments, environment⟩

def encodePoll (value : Kernel.NativePollEntry) : PollEntry :=
  ⟨value.descriptor.toNat, value.events.toNat⟩

def poll? (value : PollEntry) : Option Kernel.NativePollEntry := do
  let descriptor ← word? value.descriptor
  let events ← word? value.events
  return ⟨descriptor, events⟩

def encodeOperation : Kernel.NativeOperation → Operation
  | .vfs operation => .vfs (encodeVfs operation)
  | .socketPair domain socketType protocol => .socketPair (domain.toNat) (socketType.toNat) (protocol.toNat)
  | .fcntl fd command argument => .fcntl (fd.toNat) (command.toNat) (argument.toNat)
  | .duplicate source target flags => .duplicate (source.toNat) (target.toNat) (flags.toNat)
  | .send fd bytes extent flags => .send (fd.toNat) (encodeBytes bytes) (extent.toNat) (flags.toNat)
  | .receive fd extent flags => .receive (fd.toNat) (extent.toNat) (flags.toNat)
  | .shutdown fd how => .shutdown (fd.toNat) (how.toNat)
  | .poll entries timeout => .poll (entries.map encodePoll) (timeout.toNat)
  | .clock clockId => .clock (clockId.toNat)
  | .signal pid signal => .signal (pid.toNat) (signal.toNat)
  | .waitPid pid options => .waitPid (pid.toNat) (options.toNat)
  | .spawn arguments => .spawn (encodeSpawn arguments)
  | .exec arguments => .exec (encodeExec arguments)

def operation? : Operation → Option Kernel.NativeOperation
  | .vfs operation => do
    let decoded_operation ← vfs? operation
    return .vfs decoded_operation
  | .socketPair domain socketType protocol => do
    let decoded_domain ← word? domain
    let decoded_socketType ← word? socketType
    let decoded_protocol ← word? protocol
    return .socketPair decoded_domain decoded_socketType decoded_protocol
  | .fcntl fd command argument => do
    let decoded_fd ← word? fd
    let decoded_command ← word? command
    let decoded_argument ← word? argument
    return .fcntl decoded_fd decoded_command decoded_argument
  | .duplicate source target flags => do
    let decoded_source ← word? source
    let decoded_target ← word? target
    let decoded_flags ← word? flags
    return .duplicate decoded_source decoded_target decoded_flags
  | .send fd bytes extent flags => do
    let decoded_fd ← word? fd
    let decoded_bytes ← bytes? bytes
    let decoded_extent ← word? extent
    let decoded_flags ← word? flags
    return .send decoded_fd decoded_bytes decoded_extent decoded_flags
  | .receive fd extent flags => do
    let decoded_fd ← word? fd
    let decoded_extent ← word? extent
    let decoded_flags ← word? flags
    return .receive decoded_fd decoded_extent decoded_flags
  | .shutdown fd how => do
    let decoded_fd ← word? fd
    let decoded_how ← word? how
    return .shutdown decoded_fd decoded_how
  | .poll entries timeout => do
    let decoded_entries ← list? poll? entries
    let decoded_timeout ← word? timeout
    return .poll decoded_entries decoded_timeout
  | .clock clockId => do
    let decoded_clockId ← word? clockId
    return .clock decoded_clockId
  | .signal pid signal => do
    let decoded_pid ← word? pid
    let decoded_signal ← word? signal
    return .signal decoded_pid decoded_signal
  | .waitPid pid options => do
    let decoded_pid ← word? pid
    let decoded_options ← word? options
    return .waitPid decoded_pid decoded_options
  | .spawn arguments => do
    let decoded_arguments ← spawn? arguments
    return .spawn decoded_arguments
  | .exec arguments => do
    let decoded_arguments ← exec? arguments
    return .exec decoded_arguments

def encodeProduct : Kernel.NativeProduct → Product
  | .none  => .none
  | .socketPair first second => .socketPair (first.toNat) (second.toNat)
  | .sent bytes => .sent (encodeBytes bytes)
  | .received bytes => .received (encodeBytes bytes)
  | .created child => .created (child)
  | .executed image => .executed (image)
  | .reaped child status => .reaped (child) (status.toNat)

def product? : Product → Option Kernel.NativeProduct
  | .none  => do
    return .none
  | .socketPair first second => do
    let decoded_first ← word? first
    let decoded_second ← word? second
    return .socketPair decoded_first decoded_second
  | .sent bytes => do
    let decoded_bytes ← bytes? bytes
    return .sent decoded_bytes
  | .received bytes => do
    let decoded_bytes ← bytes? bytes
    return .received decoded_bytes
  | .created child => do
    return .created child
  | .executed image => do
    return .executed image
  | .reaped child status => do
    let decoded_status ← word? status
    return .reaped child decoded_status

def encodeReply (reply : Filesystem.Reply) : Reply := ⟨reply.1.toNat, encodeBytes reply.2⟩

def reply? (reply : Reply) : Option Filesystem.Reply := do
  let word ← word? reply.word
  let bytes ← bytes? reply.bytes
  return (word, bytes)

@[simp] theorem word_roundtrip (word : UInt64) : word? word.toNat = some word := by
  simp only [word?, UInt64.toNat_lt, ↓reduceIte, UInt64.ofNat_toNat]

@[simp] theorem byte_roundtrip (byte : UInt8) : byte? byte.toNat = some byte := by
  have bounded : byte.toNat < 256 := byte.toNat_lt
  simp only [byte?, bounded, ↓reduceIte, UInt8.ofNat_toNat]

theorem word_exact {value : Nat} {word : UInt64} (accepted : word? value = some word) :
    word.toNat = value ∧ value < 2 ^ 64 := by
  unfold word? at accepted
  split at accepted
  · rename_i bounded
    cases accepted
    exact ⟨UInt64.toNat_ofNat_of_lt' bounded, bounded⟩
  · cases accepted

theorem byte_exact {value : Nat} {byte : UInt8} (accepted : byte? value = some byte) :
    byte.toNat = value ∧ value < 256 := by
  unfold byte? at accepted
  split at accepted
  · rename_i bounded
    cases accepted
    exact ⟨UInt8.toNat_ofNat_of_lt' bounded, bounded⟩
  · cases accepted

theorem list_roundtrip {α β : Type} (read : α → Option β) (write : β → α)
    (each : ∀ value, read (write value) = some value) (values : List β) :
    list? read (values.map write) = some values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [list?, each, ih]

theorem list_exact {α β : Type} (read : α → Option β) (write : β → α)
    (each : ∀ code value, read code = some value → write value = code)
    {codes : List α} {values : List β} (accepted : list? read codes = some values) :
    values.map write = codes := by
  induction codes generalizing values with
  | nil => cases accepted; rfl
  | cons head tail ih =>
    simp only [list?] at accepted
    cases first : read head with
    | none => simp only [first, bind, Option.bind] at accepted; cases accepted
    | some value =>
      simp only [first, bind, Option.bind] at accepted
      cases rest : list? read tail with
      | none => simp only [rest] at accepted; cases accepted
      | some remaining =>
        simp only [rest, pure] at accepted
        cases accepted
        simp only [List.map_cons, each _ _ first, ih rest]

@[simp] theorem bytes_roundtrip (bytes : ByteArray) : bytes? (encodeBytes bytes) = some bytes := by
  cases bytes
  simp only [bytes?, encodeBytes, list_roundtrip byte? UInt8.toNat byte_roundtrip,
    bind, Option.bind, pure, Array.toArray_toList]

theorem bytes_exact {code : List Nat} {bytes : ByteArray} (accepted : bytes? code = some bytes) :
    encodeBytes bytes = code := by
  unfold bytes? at accepted
  cases parsed : list? byte? code with
  | none => simp only [parsed, bind, Option.bind] at accepted; cases accepted
  | some values =>
    simp only [parsed, bind, Option.bind, pure] at accepted
    cases accepted
    simp only [encodeBytes]
    exact list_exact byte? UInt8.toNat (fun _ _ proof => (byte_exact proof).1) parsed

@[simp] theorem bytes_list_roundtrip (values : List ByteArray) :
    list? bytes? (values.map encodeBytes) = some values :=
  list_roundtrip bytes? encodeBytes bytes_roundtrip values

theorem bytes_list_exact {codes : List (List Nat)} {values : List ByteArray}
    (accepted : list? bytes? codes = some values) : values.map encodeBytes = codes :=
  list_exact bytes? encodeBytes (fun _ _ proof => bytes_exact proof) accepted

@[simp] theorem op_roundtrip (op : Filesystem.Op) : op? op.code.toNat = some op := by
  cases op <;> rfl

theorem op_exact {code : Nat} {op : Filesystem.Op} (accepted : op? code = some op) :
    op.code.toNat = code := by
  unfold op? at accepted
  split at accepted <;> cases accepted <;> rfl

@[simp] theorem request_roundtrip (value : Filesystem.Request) :
    request? (encodeRequest value) = some value := by
  cases value <;> simp [encodeRequest, request?]

@[simp] theorem vfs_roundtrip (value : Kernel.NativeVfsOperation) :
    vfs? (encodeVfs value) = some value := by
  cases value <;> simp [encodeVfs, vfs?]

@[simp] theorem action_roundtrip (value : Kernel.NativeFileAction) :
    action? (encodeAction value) = some value := by
  cases value <;> simp [encodeAction, action?]

@[simp] theorem action_list_roundtrip (values : List Kernel.NativeFileAction) :
    list? action? (values.map encodeAction) = some values :=
  list_roundtrip action? encodeAction action_roundtrip values

@[simp] theorem attributes_roundtrip (value : Kernel.NativeSpawnAttributes) :
    attributes? (encodeAttributes value) = some value := by
  cases value <;> simp [encodeAttributes, attributes?]

@[simp] theorem spawn_roundtrip (value : Kernel.NativeSpawn) :
    spawn? (encodeSpawn value) = some value := by
  cases value <;> simp [encodeSpawn, spawn?]

@[simp] theorem exec_roundtrip (value : Kernel.NativeExec) :
    exec? (encodeExec value) = some value := by
  cases value <;> simp [encodeExec, exec?]

@[simp] theorem poll_roundtrip (value : Kernel.NativePollEntry) :
    poll? (encodePoll value) = some value := by
  cases value <;> simp [encodePoll, poll?]

@[simp] theorem poll_list_roundtrip (values : List Kernel.NativePollEntry) :
    list? poll? (values.map encodePoll) = some values :=
  list_roundtrip poll? encodePoll poll_roundtrip values

@[simp] theorem operation_roundtrip (value : Kernel.NativeOperation) :
    operation? (encodeOperation value) = some value := by
  cases value <;> simp [encodeOperation, operation?]

@[simp] theorem product_roundtrip (value : Kernel.NativeProduct) :
    product? (encodeProduct value) = some value := by
  cases value <;> simp [encodeProduct, product?]

@[simp] theorem reply_roundtrip (reply : Filesystem.Reply) : reply? (encodeReply reply) = some reply := by
  cases reply
  simp [reply?, encodeReply]

-- §AR-host-boundary.primitives: Accepted codes preserve every original argument and raw byte.
theorem request_exact {code : Request} {value : Filesystem.Request}
    (accepted : request? code = some value) : encodeRequest value = code := by
  cases code with
  | mk op first second third left right =>
    simp only [request?] at accepted
    cases parsed_op : op? op with
    | none => simp [parsed_op] at accepted
    | some decoded_op =>
      simp [parsed_op] at accepted
      cases parsed_first : word? first with
      | none => simp [parsed_first] at accepted
      | some decoded_first =>
        simp [parsed_first] at accepted
        cases parsed_second : word? second with
        | none => simp [parsed_second] at accepted
        | some decoded_second =>
          simp [parsed_second] at accepted
          cases parsed_third : word? third with
          | none => simp [parsed_third] at accepted
          | some decoded_third =>
            simp [parsed_third] at accepted
            cases parsed_left : bytes? left with
            | none => simp [parsed_left] at accepted
            | some decoded_left =>
              simp [parsed_left] at accepted
              cases parsed_right : bytes? right with
              | none => simp [parsed_right] at accepted
              | some decoded_right =>
                simp [parsed_right] at accepted
                cases accepted
                have field_op := op_exact parsed_op
                have field_first := (word_exact parsed_first).1
                have field_second := (word_exact parsed_second).1
                have field_third := (word_exact parsed_third).1
                have field_left := bytes_exact parsed_left
                have field_right := bytes_exact parsed_right
                simp only [encodeRequest, field_op, field_first, field_second, field_third, field_left, field_right]

theorem vfs_exact {code : VfsOperation} {value : Kernel.NativeVfsOperation}
    (accepted : vfs? code = some value) : encodeVfs value = code := by
  cases code with
  | setEncryptionPolicy fd policy =>
    simp only [vfs?] at accepted
    cases parsedFd : word? fd with
    | none => simp [parsedFd] at accepted
    | some actualFd =>
      simp [parsedFd] at accepted
      cases parsedPolicy : bytes? policy with
      | none => simp [parsedPolicy] at accepted
      | some actualPolicy =>
        simp [parsedPolicy] at accepted
        cases accepted
        simp only [encodeVfs, (word_exact parsedFd).1, bytes_exact parsedPolicy]
  | adapted request =>
    simp only [vfs?] at accepted
    cases parsed_request : request? request with
    | none => simp [parsed_request] at accepted
    | some decoded_request =>
      simp [parsed_request] at accepted
      cases accepted
      have field_request := request_exact parsed_request
      simp only [encodeVfs, field_request]
  | linkAt sourceDirectory source targetDirectory target flags =>
    simp only [vfs?] at accepted
    cases parsed_sourceDirectory : word? sourceDirectory with
    | none => simp [parsed_sourceDirectory] at accepted
    | some decoded_sourceDirectory =>
      simp [parsed_sourceDirectory] at accepted
      cases parsed_source : bytes? source with
      | none => simp [parsed_source] at accepted
      | some decoded_source =>
        simp [parsed_source] at accepted
        cases parsed_targetDirectory : word? targetDirectory with
        | none => simp [parsed_targetDirectory] at accepted
        | some decoded_targetDirectory =>
          simp [parsed_targetDirectory] at accepted
          cases parsed_target : bytes? target with
          | none => simp [parsed_target] at accepted
          | some decoded_target =>
            simp [parsed_target] at accepted
            cases parsed_flags : word? flags with
            | none => simp [parsed_flags] at accepted
            | some decoded_flags =>
              simp [parsed_flags] at accepted
              cases accepted
              have field_sourceDirectory := (word_exact parsed_sourceDirectory).1
              have field_source := bytes_exact parsed_source
              have field_targetDirectory := (word_exact parsed_targetDirectory).1
              have field_target := bytes_exact parsed_target
              have field_flags := (word_exact parsed_flags).1
              simp only [encodeVfs, field_sourceDirectory, field_source, field_targetDirectory, field_target, field_flags]
  | symlinkAt contents directory name =>
    simp only [vfs?] at accepted
    cases parsed_contents : bytes? contents with
    | none => simp [parsed_contents] at accepted
    | some decoded_contents =>
      simp [parsed_contents] at accepted
      cases parsed_directory : word? directory with
      | none => simp [parsed_directory] at accepted
      | some decoded_directory =>
        simp [parsed_directory] at accepted
        cases parsed_name : bytes? name with
        | none => simp [parsed_name] at accepted
        | some decoded_name =>
          simp [parsed_name] at accepted
          cases accepted
          have field_contents := bytes_exact parsed_contents
          have field_directory := (word_exact parsed_directory).1
          have field_name := bytes_exact parsed_name
          simp only [encodeVfs, field_contents, field_directory, field_name]
  | renameAt sourceDirectory source targetDirectory target flags =>
    simp only [vfs?] at accepted
    cases parsed_sourceDirectory : word? sourceDirectory with
    | none => simp [parsed_sourceDirectory] at accepted
    | some decoded_sourceDirectory =>
      simp [parsed_sourceDirectory] at accepted
      cases parsed_source : bytes? source with
      | none => simp [parsed_source] at accepted
      | some decoded_source =>
        simp [parsed_source] at accepted
        cases parsed_targetDirectory : word? targetDirectory with
        | none => simp [parsed_targetDirectory] at accepted
        | some decoded_targetDirectory =>
          simp [parsed_targetDirectory] at accepted
          cases parsed_target : bytes? target with
          | none => simp [parsed_target] at accepted
          | some decoded_target =>
            simp [parsed_target] at accepted
            cases parsed_flags : word? flags with
            | none => simp [parsed_flags] at accepted
            | some decoded_flags =>
              simp [parsed_flags] at accepted
              cases accepted
              have field_sourceDirectory := (word_exact parsed_sourceDirectory).1
              have field_source := bytes_exact parsed_source
              have field_targetDirectory := (word_exact parsed_targetDirectory).1
              have field_target := bytes_exact parsed_target
              have field_flags := (word_exact parsed_flags).1
              simp only [encodeVfs, field_sourceDirectory, field_source, field_targetDirectory, field_target, field_flags]
  | chdir path =>
    simp only [vfs?] at accepted
    cases parsed_path : bytes? path with
    | none => simp [parsed_path] at accepted
    | some decoded_path =>
      simp [parsed_path] at accepted
      cases accepted
      have field_path := bytes_exact parsed_path
      simp only [encodeVfs, field_path]
  | fchdir fd =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases accepted
      have field_fd := (word_exact parsed_fd).1
      simp only [encodeVfs, field_fd]
  | fchmod fd mode =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_mode : word? mode with
      | none => simp [parsed_mode] at accepted
      | some decoded_mode =>
        simp [parsed_mode] at accepted
        cases accepted
        have field_fd := (word_exact parsed_fd).1
        have field_mode := (word_exact parsed_mode).1
        simp only [encodeVfs, field_fd, field_mode]
  | fchown fd owner group =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_owner : word? owner with
      | none => simp [parsed_owner] at accepted
      | some decoded_owner =>
        simp [parsed_owner] at accepted
        cases parsed_group : word? group with
        | none => simp [parsed_group] at accepted
        | some decoded_group =>
          simp [parsed_group] at accepted
          cases accepted
          have field_fd := (word_exact parsed_fd).1
          have field_owner := (word_exact parsed_owner).1
          have field_group := (word_exact parsed_group).1
          simp only [encodeVfs, field_fd, field_owner, field_group]
  | truncate fd extent =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_extent : word? extent with
      | none => simp [parsed_extent] at accepted
      | some decoded_extent =>
        simp [parsed_extent] at accepted
        cases accepted
        have field_fd := (word_exact parsed_fd).1
        have field_extent := (word_exact parsed_extent).1
        simp only [encodeVfs, field_fd, field_extent]
  | seek fd offset whence =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_offset : word? offset with
      | none => simp [parsed_offset] at accepted
      | some decoded_offset =>
        simp [parsed_offset] at accepted
        cases parsed_whence : word? whence with
        | none => simp [parsed_whence] at accepted
        | some decoded_whence =>
          simp [parsed_whence] at accepted
          cases accepted
          have field_fd := (word_exact parsed_fd).1
          have field_offset := (word_exact parsed_offset).1
          have field_whence := (word_exact parsed_whence).1
          simp only [encodeVfs, field_fd, field_offset, field_whence]
  | pwrite fd bytes extent offset =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_bytes : bytes? bytes with
      | none => simp [parsed_bytes] at accepted
      | some decoded_bytes =>
        simp [parsed_bytes] at accepted
        cases parsed_extent : word? extent with
        | none => simp [parsed_extent] at accepted
        | some decoded_extent =>
          simp [parsed_extent] at accepted
          cases parsed_offset : word? offset with
          | none => simp [parsed_offset] at accepted
          | some decoded_offset =>
            simp [parsed_offset] at accepted
            cases accepted
            have field_fd := (word_exact parsed_fd).1
            have field_bytes := bytes_exact parsed_bytes
            have field_extent := (word_exact parsed_extent).1
            have field_offset := (word_exact parsed_offset).1
            simp only [encodeVfs, field_fd, field_bytes, field_extent, field_offset]
  | setInodeFlags fd flags =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_flags : word? flags with
      | none => simp [parsed_flags] at accepted
      | some decoded_flags =>
        simp [parsed_flags] at accepted
        cases accepted
        have field_fd := (word_exact parsed_fd).1
        have field_flags := (word_exact parsed_flags).1
        simp only [encodeVfs, field_fd, field_flags]
  | setAttribute fd name value flags =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_name : bytes? name with
      | none => simp [parsed_name] at accepted
      | some decoded_name =>
        simp [parsed_name] at accepted
        cases parsed_value : bytes? value with
        | none => simp [parsed_value] at accepted
        | some decoded_value =>
          simp [parsed_value] at accepted
          cases parsed_flags : word? flags with
          | none => simp [parsed_flags] at accepted
          | some decoded_flags =>
            simp [parsed_flags] at accepted
            cases accepted
            have field_fd := (word_exact parsed_fd).1
            have field_name := bytes_exact parsed_name
            have field_value := bytes_exact parsed_value
            have field_flags := (word_exact parsed_flags).1
            simp only [encodeVfs, field_fd, field_name, field_value, field_flags]
  | removeAttribute fd name =>
    simp only [vfs?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_name : bytes? name with
      | none => simp [parsed_name] at accepted
      | some decoded_name =>
        simp [parsed_name] at accepted
        cases accepted
        have field_fd := (word_exact parsed_fd).1
        have field_name := bytes_exact parsed_name
        simp only [encodeVfs, field_fd, field_name]

  | fchmodAt directory path mode flags =>
    simp only [vfs?] at accepted
    cases parsed_directory : word? directory with
    | none => simp [parsed_directory] at accepted
    | some decoded_directory =>
      simp [parsed_directory] at accepted
      cases parsed_path : bytes? path with
      | none => simp [parsed_path] at accepted
      | some decoded_path =>
        simp [parsed_path] at accepted
        cases parsed_mode : word? mode with
        | none => simp [parsed_mode] at accepted
        | some decoded_mode =>
          simp [parsed_mode] at accepted
          cases parsed_flags : word? flags with
          | none => simp [parsed_flags] at accepted
          | some decoded_flags =>
            simp [parsed_flags] at accepted
            cases accepted
            have field_directory := (word_exact parsed_directory).1
            have field_path := bytes_exact parsed_path
            have field_mode := (word_exact parsed_mode).1
            have field_flags := (word_exact parsed_flags).1
            simp only [encodeVfs, field_directory, field_path, field_mode, field_flags]
  | fchownAt directory path owner group flags =>
    simp only [vfs?] at accepted
    cases parsed_directory : word? directory with
    | none => simp [parsed_directory] at accepted
    | some decoded_directory =>
      simp [parsed_directory] at accepted
      cases parsed_path : bytes? path with
      | none => simp [parsed_path] at accepted
      | some decoded_path =>
        simp [parsed_path] at accepted
        cases parsed_owner : word? owner with
        | none => simp [parsed_owner] at accepted
        | some decoded_owner =>
          simp [parsed_owner] at accepted
          cases parsed_group : word? group with
          | none => simp [parsed_group] at accepted
          | some decoded_group =>
            simp [parsed_group] at accepted
            cases parsed_flags : word? flags with
            | none => simp [parsed_flags] at accepted
            | some decoded_flags =>
              simp [parsed_flags] at accepted
              cases accepted
              have field_directory := (word_exact parsed_directory).1
              have field_path := bytes_exact parsed_path
              have field_owner := (word_exact parsed_owner).1
              have field_group := (word_exact parsed_group).1
              have field_flags := (word_exact parsed_flags).1
              simp only [encodeVfs, field_directory, field_path, field_owner, field_group, field_flags]

theorem action_exact {code : FileAction} {value : Kernel.NativeFileAction}
    (accepted : action? code = some value) : encodeAction value = code := by
  cases code with
  | close fd =>
    simp only [action?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases accepted
      have field_fd := (word_exact parsed_fd).1
      simp only [encodeAction, field_fd]
  | duplicate source target =>
    simp only [action?] at accepted
    cases parsed_source : word? source with
    | none => simp [parsed_source] at accepted
    | some decoded_source =>
      simp [parsed_source] at accepted
      cases parsed_target : word? target with
      | none => simp [parsed_target] at accepted
      | some decoded_target =>
        simp [parsed_target] at accepted
        cases accepted
        have field_source := (word_exact parsed_source).1
        have field_target := (word_exact parsed_target).1
        simp only [encodeAction, field_source, field_target]
  | closeFrom minimum =>
    simp only [action?] at accepted
    cases parsed_minimum : word? minimum with
    | none => simp [parsed_minimum] at accepted
    | some decoded_minimum =>
      simp [parsed_minimum] at accepted
      cases accepted
      have field_minimum := (word_exact parsed_minimum).1
      simp only [encodeAction, field_minimum]
  | «open» fd path flags mode =>
    simp only [action?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_path : bytes? path with
      | none => simp [parsed_path] at accepted
      | some decoded_path =>
        simp [parsed_path] at accepted
        cases parsed_flags : word? flags with
        | none => simp [parsed_flags] at accepted
        | some decoded_flags =>
          simp [parsed_flags] at accepted
          cases parsed_mode : word? mode with
          | none => simp [parsed_mode] at accepted
          | some decoded_mode =>
            simp [parsed_mode] at accepted
            cases accepted
            have field_fd := (word_exact parsed_fd).1
            have field_path := bytes_exact parsed_path
            have field_flags := (word_exact parsed_flags).1
            have field_mode := (word_exact parsed_mode).1
            simp only [encodeAction, field_fd, field_path, field_flags, field_mode]
  | chdir path =>
    simp only [action?] at accepted
    cases parsed_path : bytes? path with
    | none => simp [parsed_path] at accepted
    | some decoded_path =>
      simp [parsed_path] at accepted
      cases accepted
      have field_path := bytes_exact parsed_path
      simp only [encodeAction, field_path]
  | fchdir fd =>
    simp only [action?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases accepted
      have field_fd := (word_exact parsed_fd).1
      simp only [encodeAction, field_fd]

theorem action_list_exact {codes : List FileAction} {values : List Kernel.NativeFileAction}
    (accepted : list? action? codes = some values) : values.map encodeAction = codes :=
  list_exact action? encodeAction (fun _ _ proof => action_exact proof) accepted

theorem attributes_exact {code : SpawnAttributes} {value : Kernel.NativeSpawnAttributes}
    (accepted : attributes? code = some value) : encodeAttributes value = code := by
  cases code with
  | mk flags processGroup signalMask signalDefault schedulingPolicy schedulingPriority =>
    simp only [attributes?] at accepted
    cases parsed_flags : word? flags with
    | none => simp [parsed_flags] at accepted
    | some decoded_flags =>
      simp [parsed_flags] at accepted
      cases parsed_processGroup : word? processGroup with
      | none => simp [parsed_processGroup] at accepted
      | some decoded_processGroup =>
        simp [parsed_processGroup] at accepted
        cases parsed_schedulingPolicy : word? schedulingPolicy with
        | none => simp [parsed_schedulingPolicy] at accepted
        | some decoded_schedulingPolicy =>
          simp [parsed_schedulingPolicy] at accepted
          cases parsed_schedulingPriority : word? schedulingPriority with
          | none => simp [parsed_schedulingPriority] at accepted
          | some decoded_schedulingPriority =>
            simp [parsed_schedulingPriority] at accepted
            cases accepted
            have field_flags := (word_exact parsed_flags).1
            have field_processGroup := (word_exact parsed_processGroup).1
            have field_schedulingPolicy := (word_exact parsed_schedulingPolicy).1
            have field_schedulingPriority := (word_exact parsed_schedulingPriority).1
            simp only [encodeAttributes, field_flags, field_processGroup, field_schedulingPolicy, field_schedulingPriority]

theorem spawn_exact {code : Spawn} {value : Kernel.NativeSpawn}
    (accepted : spawn? code = some value) : encodeSpawn value = code := by
  cases code with
  | mk path arguments environment actions attributes =>
    simp only [spawn?] at accepted
    cases parsed_path : bytes? path with
    | none => simp [parsed_path] at accepted
    | some decoded_path =>
      simp [parsed_path] at accepted
      cases parsed_arguments : list? bytes? arguments with
      | none => simp [parsed_arguments] at accepted
      | some decoded_arguments =>
        simp [parsed_arguments] at accepted
        cases parsed_environment : list? bytes? environment with
        | none => simp [parsed_environment] at accepted
        | some decoded_environment =>
          simp [parsed_environment] at accepted
          cases parsed_actions : list? action? actions with
          | none => simp [parsed_actions] at accepted
          | some decoded_actions =>
            simp [parsed_actions] at accepted
            cases parsed_attributes : attributes? attributes with
            | none => simp [parsed_attributes] at accepted
            | some decoded_attributes =>
              simp [parsed_attributes] at accepted
              cases accepted
              have field_path := bytes_exact parsed_path
              have field_arguments := bytes_list_exact parsed_arguments
              have field_environment := bytes_list_exact parsed_environment
              have field_actions := action_list_exact parsed_actions
              have field_attributes := attributes_exact parsed_attributes
              simp only [encodeSpawn, field_path, field_arguments, field_environment, field_actions, field_attributes]

theorem exec_exact {code : Exec} {value : Kernel.NativeExec}
    (accepted : exec? code = some value) : encodeExec value = code := by
  cases code with
  | mk path arguments environment =>
    simp only [exec?] at accepted
    cases parsed_path : bytes? path with
    | none => simp [parsed_path] at accepted
    | some decoded_path =>
      simp [parsed_path] at accepted
      cases parsed_arguments : list? bytes? arguments with
      | none => simp [parsed_arguments] at accepted
      | some decoded_arguments =>
        simp [parsed_arguments] at accepted
        cases parsed_environment : list? bytes? environment with
        | none => simp [parsed_environment] at accepted
        | some decoded_environment =>
          simp [parsed_environment] at accepted
          cases accepted
          have field_path := bytes_exact parsed_path
          have field_arguments := bytes_list_exact parsed_arguments
          have field_environment := bytes_list_exact parsed_environment
          simp only [encodeExec, field_path, field_arguments, field_environment]

theorem poll_exact {code : PollEntry} {value : Kernel.NativePollEntry}
    (accepted : poll? code = some value) : encodePoll value = code := by
  cases code with
  | mk descriptor events =>
    simp only [poll?] at accepted
    cases parsed_descriptor : word? descriptor with
    | none => simp [parsed_descriptor] at accepted
    | some decoded_descriptor =>
      simp [parsed_descriptor] at accepted
      cases parsed_events : word? events with
      | none => simp [parsed_events] at accepted
      | some decoded_events =>
        simp [parsed_events] at accepted
        cases accepted
        have field_descriptor := (word_exact parsed_descriptor).1
        have field_events := (word_exact parsed_events).1
        simp only [encodePoll, field_descriptor, field_events]

theorem poll_list_exact {codes : List PollEntry} {values : List Kernel.NativePollEntry}
    (accepted : list? poll? codes = some values) : values.map encodePoll = codes :=
  list_exact poll? encodePoll (fun _ _ proof => poll_exact proof) accepted

theorem operation_exact {code : Operation} {value : Kernel.NativeOperation}
    (accepted : operation? code = some value) : encodeOperation value = code := by
  cases code with
  | vfs operation =>
    simp only [operation?] at accepted
    cases parsed_operation : vfs? operation with
    | none => simp [parsed_operation] at accepted
    | some decoded_operation =>
      simp [parsed_operation] at accepted
      cases accepted
      have field_operation := vfs_exact parsed_operation
      simp only [encodeOperation, field_operation]
  | socketPair domain socketType protocol =>
    simp only [operation?] at accepted
    cases parsed_domain : word? domain with
    | none => simp [parsed_domain] at accepted
    | some decoded_domain =>
      simp [parsed_domain] at accepted
      cases parsed_socketType : word? socketType with
      | none => simp [parsed_socketType] at accepted
      | some decoded_socketType =>
        simp [parsed_socketType] at accepted
        cases parsed_protocol : word? protocol with
        | none => simp [parsed_protocol] at accepted
        | some decoded_protocol =>
          simp [parsed_protocol] at accepted
          cases accepted
          have field_domain := (word_exact parsed_domain).1
          have field_socketType := (word_exact parsed_socketType).1
          have field_protocol := (word_exact parsed_protocol).1
          simp only [encodeOperation, field_domain, field_socketType, field_protocol]
  | fcntl fd command argument =>
    simp only [operation?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_command : word? command with
      | none => simp [parsed_command] at accepted
      | some decoded_command =>
        simp [parsed_command] at accepted
        cases parsed_argument : word? argument with
        | none => simp [parsed_argument] at accepted
        | some decoded_argument =>
          simp [parsed_argument] at accepted
          cases accepted
          have field_fd := (word_exact parsed_fd).1
          have field_command := (word_exact parsed_command).1
          have field_argument := (word_exact parsed_argument).1
          simp only [encodeOperation, field_fd, field_command, field_argument]
  | duplicate source target flags =>
    simp only [operation?] at accepted
    cases parsed_source : word? source with
    | none => simp [parsed_source] at accepted
    | some decoded_source =>
      simp [parsed_source] at accepted
      cases parsed_target : word? target with
      | none => simp [parsed_target] at accepted
      | some decoded_target =>
        simp [parsed_target] at accepted
        cases parsed_flags : word? flags with
        | none => simp [parsed_flags] at accepted
        | some decoded_flags =>
          simp [parsed_flags] at accepted
          cases accepted
          have field_source := (word_exact parsed_source).1
          have field_target := (word_exact parsed_target).1
          have field_flags := (word_exact parsed_flags).1
          simp only [encodeOperation, field_source, field_target, field_flags]
  | send fd bytes extent flags =>
    simp only [operation?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_bytes : bytes? bytes with
      | none => simp [parsed_bytes] at accepted
      | some decoded_bytes =>
        simp [parsed_bytes] at accepted
        cases parsed_extent : word? extent with
        | none => simp [parsed_extent] at accepted
        | some decoded_extent =>
          simp [parsed_extent] at accepted
          cases parsed_flags : word? flags with
          | none => simp [parsed_flags] at accepted
          | some decoded_flags =>
            simp [parsed_flags] at accepted
            cases accepted
            have field_fd := (word_exact parsed_fd).1
            have field_bytes := bytes_exact parsed_bytes
            have field_extent := (word_exact parsed_extent).1
            have field_flags := (word_exact parsed_flags).1
            simp only [encodeOperation, field_fd, field_bytes, field_extent, field_flags]
  | receive fd extent flags =>
    simp only [operation?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_extent : word? extent with
      | none => simp [parsed_extent] at accepted
      | some decoded_extent =>
        simp [parsed_extent] at accepted
        cases parsed_flags : word? flags with
        | none => simp [parsed_flags] at accepted
        | some decoded_flags =>
          simp [parsed_flags] at accepted
          cases accepted
          have field_fd := (word_exact parsed_fd).1
          have field_extent := (word_exact parsed_extent).1
          have field_flags := (word_exact parsed_flags).1
          simp only [encodeOperation, field_fd, field_extent, field_flags]
  | shutdown fd how =>
    simp only [operation?] at accepted
    cases parsed_fd : word? fd with
    | none => simp [parsed_fd] at accepted
    | some decoded_fd =>
      simp [parsed_fd] at accepted
      cases parsed_how : word? how with
      | none => simp [parsed_how] at accepted
      | some decoded_how =>
        simp [parsed_how] at accepted
        cases accepted
        have field_fd := (word_exact parsed_fd).1
        have field_how := (word_exact parsed_how).1
        simp only [encodeOperation, field_fd, field_how]
  | poll entries timeout =>
    simp only [operation?] at accepted
    cases parsed_entries : list? poll? entries with
    | none => simp [parsed_entries] at accepted
    | some decoded_entries =>
      simp [parsed_entries] at accepted
      cases parsed_timeout : word? timeout with
      | none => simp [parsed_timeout] at accepted
      | some decoded_timeout =>
        simp [parsed_timeout] at accepted
        cases accepted
        have field_entries := poll_list_exact parsed_entries
        have field_timeout := (word_exact parsed_timeout).1
        simp only [encodeOperation, field_entries, field_timeout]
  | clock clockId =>
    simp only [operation?] at accepted
    cases parsed_clockId : word? clockId with
    | none => simp [parsed_clockId] at accepted
    | some decoded_clockId =>
      simp [parsed_clockId] at accepted
      cases accepted
      have field_clockId := (word_exact parsed_clockId).1
      simp only [encodeOperation, field_clockId]
  | signal pid signal =>
    simp only [operation?] at accepted
    cases parsed_pid : word? pid with
    | none => simp [parsed_pid] at accepted
    | some decoded_pid =>
      simp [parsed_pid] at accepted
      cases parsed_signal : word? signal with
      | none => simp [parsed_signal] at accepted
      | some decoded_signal =>
        simp [parsed_signal] at accepted
        cases accepted
        have field_pid := (word_exact parsed_pid).1
        have field_signal := (word_exact parsed_signal).1
        simp only [encodeOperation, field_pid, field_signal]
  | waitPid pid options =>
    simp only [operation?] at accepted
    cases parsed_pid : word? pid with
    | none => simp [parsed_pid] at accepted
    | some decoded_pid =>
      simp [parsed_pid] at accepted
      cases parsed_options : word? options with
      | none => simp [parsed_options] at accepted
      | some decoded_options =>
        simp [parsed_options] at accepted
        cases accepted
        have field_pid := (word_exact parsed_pid).1
        have field_options := (word_exact parsed_options).1
        simp only [encodeOperation, field_pid, field_options]
  | spawn arguments =>
    simp only [operation?] at accepted
    cases parsed_arguments : spawn? arguments with
    | none => simp [parsed_arguments] at accepted
    | some decoded_arguments =>
      simp [parsed_arguments] at accepted
      cases accepted
      have field_arguments := spawn_exact parsed_arguments
      simp only [encodeOperation, field_arguments]
  | exec arguments =>
    simp only [operation?] at accepted
    cases parsed_arguments : exec? arguments with
    | none => simp [parsed_arguments] at accepted
    | some decoded_arguments =>
      simp [parsed_arguments] at accepted
      cases accepted
      have field_arguments := exec_exact parsed_arguments
      simp only [encodeOperation, field_arguments]

theorem product_exact {code : Product} {value : Kernel.NativeProduct}
    (accepted : product? code = some value) : encodeProduct value = code := by
  cases code with
  | none =>
    simp only [product?] at accepted
    cases accepted
    simp only [encodeProduct]
  | socketPair first second =>
    simp only [product?] at accepted
    cases parsed_first : word? first with
    | none => simp [parsed_first] at accepted
    | some decoded_first =>
      simp [parsed_first] at accepted
      cases parsed_second : word? second with
      | none => simp [parsed_second] at accepted
      | some decoded_second =>
        simp [parsed_second] at accepted
        cases accepted
        have field_first := (word_exact parsed_first).1
        have field_second := (word_exact parsed_second).1
        simp only [encodeProduct, field_first, field_second]
  | sent bytes =>
    simp only [product?] at accepted
    cases parsed_bytes : bytes? bytes with
    | none => simp [parsed_bytes] at accepted
    | some decoded_bytes =>
      simp [parsed_bytes] at accepted
      cases accepted
      have field_bytes := bytes_exact parsed_bytes
      simp only [encodeProduct, field_bytes]
  | received bytes =>
    simp only [product?] at accepted
    cases parsed_bytes : bytes? bytes with
    | none => simp [parsed_bytes] at accepted
    | some decoded_bytes =>
      simp [parsed_bytes] at accepted
      cases accepted
      have field_bytes := bytes_exact parsed_bytes
      simp only [encodeProduct, field_bytes]
  | created child =>
    simp only [product?] at accepted
    cases accepted
    simp only [encodeProduct]
  | executed image =>
    simp only [product?] at accepted
    cases accepted
    simp only [encodeProduct]
  | reaped child status =>
    simp only [product?] at accepted
    cases parsed_status : word? status with
    | none => simp [parsed_status] at accepted
    | some decoded_status =>
      simp [parsed_status] at accepted
      cases accepted
      have field_status := (word_exact parsed_status).1
      simp only [encodeProduct, field_status]


theorem reply_exact {code : Reply} {reply : Filesystem.Reply} (accepted : reply? code = some reply) :
    encodeReply reply = code := by
  cases code with
  | mk word bytes =>
    simp only [reply?] at accepted
    cases parsedWord : word? word with
    | none => simp [parsedWord] at accepted
    | some actualWord =>
      simp [parsedWord] at accepted
      cases parsedBytes : bytes? bytes with
      | none => simp [parsedBytes] at accepted
      | some actualBytes =>
        simp [parsedBytes] at accepted
        cases accepted
        simp only [encodeReply, (word_exact parsedWord).1, bytes_exact parsedBytes]

theorem operation_decode_iff (code : Operation) (value : Kernel.NativeOperation) :
    operation? code = some value ↔ encodeOperation value = code := by
  constructor
  · exact operation_exact
  · intro same
    rw [← same]
    exact operation_roundtrip value

theorem product_decode_iff (code : Product) (value : Kernel.NativeProduct) :
    product? code = some value ↔ encodeProduct value = code := by
  constructor
  · exact product_exact
  · intro same
    rw [← same]
    exact product_roundtrip value

end LeanCage.Host.NativeCode
