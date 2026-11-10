import TransportProofs.Results

namespace LeanCage.Host.Transport

namespace Witness

set_option cbv.maxSteps 2000000
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

-- §FS-host-boundary.transport: These kernel-evaluated paths exercise the maintained decoder.
def limits : Limits := ⟨3, 3, 3, 2⟩
def request : ByteArray := ⟨(List.replicate 32 (97 : UInt8)).toArray⟩
def bundle : ByteArray := ⟨(List.replicate 64 (98 : UInt8)).toArray⟩
def initial : State := { limits, expectedPrefix := identityPrefix request bundle, phase := .prefix 0 }
def headerBytes (tag reserved length : Nat) : ByteArray :=
  littleEndian 4 tag ++ littleEndian 4 reserved ++ littleEndian 8 length

def frame (tag : Tag) (payload : ByteArray) : Frame :=
  ⟨⟨headerBytes tag.code 0 payload.size, tag, payload.size⟩, payload⟩

def terminalBytes (controller retrieved error extinct : Nat) : ByteArray :=
  littleEndian 4 controller ++ littleEndian 4 retrieved ++ littleEndian 4 error ++ littleEndian 4 extinct

def report : ByteArray := "{}".toUTF8
def stdout : ByteArray := "ok".toUTF8
def terminal : Terminal := ⟨0, 0, 0, 1⟩
def terminalPayload : ByteArray := terminalBytes 0 0 0 1
def frames : List Frame := [frame .report report, frame .stdout stdout, frame .terminal terminalPayload]
def goodWire : ByteArray := identityPrefix request bundle ++
  (frame .report report).wire ++ (frame .stdout stdout).wire ++ (frame .terminal terminalPayload).wire

def result : Result := {
  report, stored := none, stdout := some stdout, stderr := none, manifest := none, blobs := [],
  terminal, frames }

def fragmented : List Event := [.data (goodWire.extract 0 1), .data (goodWire.extract 1 103),
  .data (goodWire.extract 103 121), .data (goodWire.extract 121 goodWire.size), .eof]

theorem initialized : State.init request bundle limits = .ok initial := by cbv

set_option maxRecDepth 8192 in
theorem useful_exact : (initial.run fragmented).finish = .ok result := by cbv

set_option maxRecDepth 8192 in
theorem eof_required : (initial.run [.data goodWire]).finish = .error Error.incomplete.message := by cbv

set_option maxRecDepth 8192 in
theorem truncation_rejected :
    (initial.run [.data (goodWire.extract 0 (goodWire.size - 1)), .eof]).finish =
      .error Error.incomplete.message := by cbv

set_option maxRecDepth 8192 in
theorem trailing_rejected :
    (initial.run [.data (goodWire ++ ⟨#[0]⟩), .eof]).finish = .error Error.trailing.message := by cbv

set_option maxRecDepth 8192 in
theorem eof_is_final : (initial.run [.eof, .data goodWire]).finish = .error Error.afterEof.message := by cbv

set_option maxRecDepth 8192 in
theorem duplicate_report_rejected :
    (initial.run [.data (identityPrefix request bundle ++ (frame .report report).wire ++
      (frame .report report).wire), .eof]).finish = .error Error.duplicate.message := by cbv

set_option maxRecDepth 8192 in
theorem duplicate_preserves_report :
    (initial.run [.data (identityPrefix request bundle ++ (frame .report report).wire ++
      (frame .report report).wire), .eof]).report? = some report := by cbv

set_option maxRecDepth 8192 in
theorem reserved_rejected :
    (initial.run [.data (identityPrefix request bundle ++ headerBytes 1 1 0), .eof]).finish =
      .error Error.header.message := by cbv

set_option maxRecDepth 8192 in
theorem unknown_tag_rejected :
    (initial.run [.data (identityPrefix request bundle ++ headerBytes 8 0 0), .eof]).finish =
      .error Error.header.message := by cbv

set_option maxRecDepth 8192 in
theorem maximum_uint64_rejected :
    (initial.run [.data (identityPrefix request bundle ++ headerBytes 1 0 (2^64 - 1)), .eof]).finish =
      .error Error.header.message := by cbv

set_option maxRecDepth 8192 in
theorem terminal_bounds_rejected :
    (initial.run [.data (identityPrefix request bundle ++ (frame .report report).wire ++
      (frame .terminal (terminalBytes 0 0 0 2)).wire), .eof]).finish =
      .error Error.terminal.message := by cbv

def digest : ByteArray := "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad".toUTF8
def content : ByteArray := "abc".toUTF8
def blobFrame : Frame := frame .blob (digest ++ content)
def blobFrames : List Frame := [frame .report report, blobFrame, frame .terminal terminalPayload]
def blobResult : Result := { result with stdout := none, blobs := [⟨digest, content⟩], frames := blobFrames }
def blobWire : ByteArray := identityPrefix request bundle ++ (frame .report report).wire ++
  blobFrame.wire ++ (frame .terminal terminalPayload).wire

-- Content identity is validated by Artifacts; this witness establishes exact transport bytes.
theorem useful_blob_exact : (initial.run [.data blobWire, .eof]).finish = .ok blobResult := by cbv

def emptyDigest : ByteArray :=
  "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855".toUTF8

theorem duplicate_blob_rejected :
    (initial.run [.data (identityPrefix request bundle ++ (frame .blob emptyDigest).wire ++
      (frame .blob emptyDigest).wire), .eof]).finish = .error Error.duplicate.message := by cbv

theorem aggregate_bytes_rejected :
    (initial.run [.data (identityPrefix request bundle ++ blobFrame.wire ++
      (frame .blob (emptyDigest ++ "x".toUTF8)).wire), .eof]).finish =
      .error Error.aggregate.message := by cbv

theorem malformed_digest_rejected :
    (initial.run [.data (identityPrefix request bundle ++
      (frame .blob ⟨(List.replicate 64 (65 : UInt8)).toArray⟩).wire), .eof]).finish =
      .error Error.digest.message := by cbv

theorem short_blob_rejected :
    (initial.run [.data (identityPrefix request bundle ++ (frame .blob content).wire), .eof]).finish =
      .error Error.aggregate.message := by cbv

theorem missing_report_rejected :
    (initial.run [.data (identityPrefix request bundle ++ (frame .terminal terminalPayload).wire), .eof]).finish =
      .error Error.missingReport.message := by cbv

theorem mismatched_identity_rejected :
    (initial.run [.data ⟨#[0]⟩, .eof]).finish = .error Error.identity.message := by cbv

end Witness

end LeanCage.Host.Transport
