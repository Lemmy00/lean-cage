import LeanCageHost.Bytes
import Std

namespace LeanCage.Host.Transport

-- §FS-host-boundary.transport: Policy caps are checked before a stream retains any bytes.
structure Limits where
  stdoutMax : Nat
  stderrMax : Nat
  workspaceMax : Nat
  inodesMax : Nat
  deriving DecidableEq, Repr

def Limits.Valid (limits : Limits) : Prop :=
  limits.stdoutMax ≤ captureMax ∧ limits.stderrMax ≤ captureMax ∧
    limits.workspaceMax ≤ LeanCage.Host.workspaceMax ∧ limits.inodesMax ≤ inodeMax

instance (limits : Limits) : Decidable limits.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Limits.valid (limits : Limits) : Bool := decide limits.Valid

inductive Tag where
  | report | stored | stdout | stderr | export | blob | terminal
  deriving DecidableEq, BEq, Repr

def Tag.code : Tag → Nat
  | .report => 1 | .stored => 2 | .stdout => 3 | .stderr => 4
  | .export => 5 | .blob => 6 | .terminal => 7

def Tag.ofCode : Nat → Option Tag
  | 1 => some .report | 2 => some .stored | 3 => some .stdout | 4 => some .stderr
  | 5 => some .export | 6 => some .blob | 7 => some .terminal | _ => none

def Tag.cap (limits : Limits) : Tag → Nat
  | .report | .stored => reportMax
  | .stdout => limits.stdoutMax
  | .stderr => limits.stderrMax
  | .export => manifestMax
  | .blob => 64 + limits.workspaceMax
  | .terminal => 16

inductive Error where
  | invalidLimits | invalidIdentity | identity | chunk | header | duplicate | aggregate
  | digest | terminal | trailing | afterEof | incomplete | missingReport
  deriving DecidableEq, Repr

def Error.message : Error → String
  | .invalidLimits => "unsupported transport limits"
  | .invalidIdentity => "invalid request/bundle identity"
  | .identity => "VM result request/bundle identity differs"
  | .chunk => "VM result chunk exceeds 65536 bytes"
  | .header => "invalid or oversized result record"
  | .duplicate => "duplicate result record or blob"
  | .aggregate => "export aggregate bound exceeded"
  | .digest => "invalid blob digest encoding"
  | .terminal => "invalid terminal result"
  | .trailing => "trailing result bytes"
  | .afterEof => "data after result EOF"
  | .incomplete => "incomplete VM result channel"
  | .missingReport => "missing controller result"

def magic : ByteArray := ⟨#[76, 67, 86, 77, 49, 0, 0, 0]⟩

def identityPrefix (request bundle : ByteArray) : ByteArray := magic ++ request ++ bundle

def ascii (bytes : ByteArray) : Bool := bytes.data.all (fun byte => byte.toNat < 128)

def lowerHex (bytes : ByteArray) : Bool := bytes.data.all fun byte =>
  (48 ≤ byte.toNat && byte.toNat ≤ 57) || (97 ≤ byte.toNat && byte.toNat ≤ 102)

-- §FS-host-boundary.transport: Decode every little-endian bit in Nat, without machine overflow.
def word (bytes : ByteArray) (offset width : Nat) : Nat :=
  fromLittleEndian (bytes.extract offset (offset + width))

structure Header where
  raw : ByteArray
  tag : Tag
  length : Nat
  deriving DecidableEq

def Header.parse (limits : Limits) (bytes : ByteArray) : Except Error Header :=
  if bytes.size = 16 ∧ word bytes 4 4 = 0 then
    match Tag.ofCode (word bytes 0 4) with
    | none => .error .header
    | some tag =>
        let length := word bytes 8 8
        if length ≤ tag.cap limits then
          if tag = .blob ∧ length < 64 then .error .aggregate
          else if tag = .terminal ∧ length ≠ 16 then .error .terminal
          else .ok ⟨bytes, tag, length⟩
        else .error .header
  else .error .header

structure Frame where
  header : Header
  payload : ByteArray
  deriving DecidableEq

def Frame.wire (frame : Frame) : ByteArray := frame.header.raw ++ frame.payload
def Frame.blobKey (frame : Frame) : ByteArray := frame.payload.extract 0 64
def Frame.blobContent (frame : Frame) : ByteArray := frame.payload.extract 64 frame.payload.size

structure Terminal where
  controller : Nat
  retrieved : Nat
  error : Nat
  extinct : Nat
  deriving DecidableEq, Repr

def Terminal.parse (bytes : ByteArray) : Except Error Terminal :=
  if bytes.size = 16 then
    let result : Terminal := ⟨word bytes 0 4, word bytes 4 4, word bytes 8 4, word bytes 12 4⟩
    if result.controller ≤ 255 ∧ result.retrieved ≤ 255 ∧ result.error ≤ 4095 ∧ result.extinct ≤ 1 then
      .ok result
    else .error .terminal
  else .error .terminal

-- §FS-host-boundary.transport: Counts include actual retained header/digest metadata.
def retainedBudget (limits : Limits) : Nat :=
  6 * (manifestMax + 16) + limits.workspaceMax + 80 * limits.inodesMax

def activeBudget (limits : Limits) : Nat := 64 + limits.workspaceMax + manifestMax + 16

inductive Phase where
  | prefix (matched : Nat)
  | header (bytes : ByteArray)
  | payload (header : Header) (bytes : ByteArray)
  | done
  | failed

inductive Event where
  | data (bytes : ByteArray)
  | eof

structure State where
  limits : Limits
  expectedPrefix : ByteArray
  phase : Phase
  framesRev : List Frame := []
  blobKeys : Std.TreeSet Nat compare := ∅
  blobCount : Nat := 0
  blobBytes : Nat := 0
  normalCount : Nat := 0
  retainedBytes : Nat := 0
  terminal : Option Terminal := none
  observedEof : Bool := false
  error : Option Error := none

def State.fail (state : State) (error : Error) : State :=
  { state with phase := .failed, error := some error }

def State.report? (state : State) : Option ByteArray :=
  (state.framesRev.find? (fun frame => frame.header.tag == .report)).map (·.payload)

def State.seen (state : State) (tag : Tag) : Bool :=
  state.framesRev.any (fun frame => frame.header.tag == tag)

def State.seenBlob (state : State) (key : ByteArray) : Bool :=
  state.blobKeys.contains (fromLittleEndian key)

-- §FS-host-boundary.transport: Invalid caller metadata is rejected before it is retained.
def State.init (request bundle : ByteArray) (limits : Limits) : Except String State :=
  if limits.Valid then
    if request.size = 32 ∧ bundle.size = 64 ∧ ascii request = true ∧ ascii bundle = true then
      .ok { limits, expectedPrefix := identityPrefix request bundle, phase := .prefix 0 }
    else .error Error.invalidIdentity.message
  else .error Error.invalidLimits.message

def State.acceptHeader (state : State) (header : Header) : Except Error Unit :=
  let fits := state.retainedBytes + 16 + header.length ≤ retainedBudget state.limits
  if header.tag = .blob then
    if state.blobCount + 1 ≤ state.limits.inodesMax ∧
        state.blobBytes + (header.length - 64) ≤ state.limits.workspaceMax ∧ fits then .ok ()
    else .error .aggregate
  else if state.seen header.tag then .error .duplicate
  else if state.normalCount + 1 ≤ 6 ∧ fits then .ok ()
  else .error .aggregate

def State.acceptBlob (state : State) (header : Header) (payload : ByteArray) : Except Error Unit :=
  if header.tag = .blob then
    let key := payload.extract 0 64
    if key.size = 64 ∧ lowerHex key = true then
      if state.seenBlob key then .error .duplicate else .ok ()
    else .error .digest
  else .ok ()

def State.nextTerminal (state : State) (header : Header) (payload : ByteArray) : Except Error (Option Terminal) :=
  if header.tag = .terminal then
    match Terminal.parse payload with
    | .ok terminal => .ok (some terminal)
    | .error error => .error error
  else .ok state.terminal

def State.append (state : State) (header : Header) (payload : ByteArray) (terminal : Option Terminal) : State :=
  let frame : Frame := ⟨header, payload⟩
  { state with
    phase := if header.tag = .terminal then .done else .header ByteArray.empty
    framesRev := frame :: state.framesRev
    blobKeys := if header.tag = .blob then state.blobKeys.insert (fromLittleEndian frame.blobKey) else state.blobKeys
    blobCount := state.blobCount + (if header.tag = .blob then 1 else 0)
    blobBytes := state.blobBytes + (if header.tag = .blob then payload.size - 64 else 0)
    normalCount := state.normalCount + (if header.tag = .blob then 0 else 1)
    retainedBytes := state.retainedBytes + 16 + payload.size
    terminal }

-- §FS-host-boundary.transport: Only a complete payload can enter the bounded frame ledger.
def State.commit? (state : State) (header : Header) (payload : ByteArray) : Except Error State :=
  match Header.parse state.limits header.raw with
  | .error error => .error error
  | .ok actual =>
    match state.acceptHeader actual with
    | .error error => .error error
    | .ok () =>
      if payload.size = actual.length then
        match state.acceptBlob actual payload with
        | .error error => .error error
        | .ok () =>
          match state.nextTerminal actual payload with
          | .error error => .error error
          | .ok terminal => .ok (state.append actual payload terminal)
      else .error .header

def State.commit (state : State) (header : Header) (payload : ByteArray) : State :=
  match state.commit? header payload with
  | .ok next => next
  | .error error => state.fail error

-- §FS-host-boundary.transport: Bounds are checked before push/extract/list allocation.
def State.byte (state : State) (byte : UInt8) : State :=
  if state.error.isSome then state else
  match state.phase with
  | .failed => state.fail .incomplete
  | .done => state.fail .trailing
  | .prefix matched =>
      if matched < state.expectedPrefix.size then
        if state.expectedPrefix[matched]! = byte then
          { state with phase := if matched + 1 = state.expectedPrefix.size then .header ByteArray.empty
              else .prefix (matched + 1) }
        else state.fail .identity
      else state.fail .identity
  | .header bytes =>
      if bytes.size < 16 then
        let complete := bytes.push byte
        if complete.size = 16 then
          match Header.parse state.limits complete with
          | .error error => state.fail error
          | .ok header =>
              match state.acceptHeader header with
              | .error error => state.fail error
              | .ok () =>
                  if header.length = 0 then state.commit header ByteArray.empty
                  else { state with phase := .payload header ByteArray.empty }
        else { state with phase := .header complete }
      else state.fail .header
  | .payload header bytes =>
      if bytes.size < header.length && header.length ≤ activeBudget state.limits then
        let complete := bytes.push byte
        if complete.size = header.length then state.commit header complete
        else { state with phase := .payload header complete }
      else state.fail .header

def State.bytes (state : State) (bytes : List UInt8) : State := bytes.foldl State.byte state

def State.step (state : State) (event : Event) : State :=
  if state.error.isSome then state else
  match event with
  | .eof => { state with observedEof := true }
  | .data bytes =>
      if bytes.size > chunkMax then state.fail .chunk
      else if state.observedEof then state.fail .afterEof
      else state.bytes bytes.data.toList

def State.run (state : State) (events : List Event) : State := events.foldl State.step state

structure Blob where
  digest : ByteArray
  content : ByteArray
  deriving DecidableEq

structure Result where
  report : ByteArray
  stored : Option ByteArray
  stdout : Option ByteArray
  stderr : Option ByteArray
  manifest : Option ByteArray
  blobs : List Blob
  terminal : Terminal
  frames : List Frame
  deriving DecidableEq

def Result.record? (frames : List Frame) (tag : Tag) : Option ByteArray :=
  (frames.find? (fun frame => frame.header.tag == tag)).map (·.payload)

-- §FS-host-boundary.transport: END or VM exit alone cannot authorize complete results.
def State.finish (state : State) : Except String Result :=
  match state.error with
  | some error => .error error.message
  | none =>
    if state.observedEof then
      match state.phase, state.terminal with
      | .done, some terminal =>
        match state.report? with
        | none => .error Error.missingReport.message
        | some report =>
          let frames := state.framesRev.reverse
          .ok {
            report := report
            stored := Result.record? frames .stored
            stdout := Result.record? frames .stdout
            stderr := Result.record? frames .stderr
            manifest := Result.record? frames .export
            blobs := frames.filterMap (fun frame => if frame.header.tag = .blob then
              some ⟨frame.blobKey, frame.blobContent⟩ else none)
            terminal := terminal
            frames := frames }
      | _, _ => .error Error.incomplete.message
    else .error Error.incomplete.message

end LeanCage.Host.Transport
