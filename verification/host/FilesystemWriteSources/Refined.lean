import FilesystemWriteSources
import FilesystemWriteSources.Publication

namespace LeanCage.Host.Kernel.WriteSources
open Filesystem

inductive RefinedCall (before : List Program.Event) (event : Program.Event) : Type 1 where
  | file (parent : UInt64) (name bytes : ByteArray) (mode : UInt64)
      (source : Slice (α := Result Unit) (Program.liftFilesystem (writeNew parent name bytes mode)) before event)
  | image (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry)
      (source : Slice (α := Result Unit) (Program.liftFilesystem (Image.create runFd bundle overlay)) before event)
  | machine (bundle : Validation.Bundle) (directory : String) (duration : Nat) (transport : Transport.State)
      (source : Slice (α := VirtualMachine.Result) (VirtualMachine.run bundle directory duration transport) before event)

theorem publication_file (caller : GatewayWire.Request) (bundle : Validation.Bundle) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Slice (Program.liftFilesystem (Publication.publish caller bundle input)) before
      (Program.filesystemPrefixEvent (request, observed))) (writing : request.op = .write) :
    Nonempty (RefinedCall before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨earlier, active, earlierTrace⟩ := selected_filesystem_source source.active
  obtain ⟨file⟩ := publish_files caller bundle input earlier request observed active writing
  have mapped : source.inside = file.context.map Program.filesystemPrefixEvent ++
      file.inside.map Program.filesystemPrefixEvent :=
    earlierTrace.trans ((congrArg (List.map Program.filesystemPrefixEvent) file.trace).trans List.map_append)
  refine ⟨.file file.parent file.name file.bytes file.mode
    ⟨source.context ++ file.context.map Program.filesystemPrefixEvent,
      file.inside.map Program.filesystemPrefixEvent, ?_, ?_⟩⟩
  · simpa only [List.map_append, List.map_singleton] using Program.lift_filesystem_prefix file.active
  · exact source.trace.trans ((congrArg (source.context ++ ·) mapped).trans
      (List.append_assoc source.context _ _).symm)

-- §FS-host-boundary.caller: Only the actual VM call can send during dispatch; validation
-- after that VM uses hashes only and cannot send on the public response channel.
theorem dispatch_machine {caller : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    (context : RunPrefixCuts.Imaged caller bundle duration)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Slice context.dispatchProgram before (Program.filesystemPrefixEvent (request, observed)))
    (writing : request.op = .write) :
    Nonempty (RefinedCall before (Program.filesystemPrefixEvent (request, observed))) := by
  rcases source with ⟨outer, inside, active, wholeTrace⟩
  unfold RunPrefixCuts.Imaged.dispatchProgram dispatchImage at active
  cases image : context.image with
  | error error =>
    rw [image] at active
    exact False.elim (Program.pure_has_no_last _ _ _ active)
  | ok value =>
    rw [image] at active
    rcases Program.last_bind_split _ _ active with machine |
        ⟨events, result, remaining, completed, checking, trace⟩
    · exact ⟨.machine bundle context.allocated.directory.path context.allocated.setup.duration
        context.allocated.setup.transport ⟨outer, inside, machine, wholeTrace⟩⟩
    · exact False.elim (selected_filesystem_profile
        (read_only_no_write (Retrieval.readOnly_hashOnly (ReceiveProofs.receive_hashOnly _ _ _ _ _))) checking writing)

-- §FS-host-boundary.ownership: Every application write has an actual exclusive-file or
-- VM-control producer. The proof keeps exact nested source arguments and preceding events.
theorem Call.refine {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Call before (Program.filesystemPrefixEvent (request, observed))) (writing : request.op = .write) :
    Nonempty (RefinedCall before (Program.filesystemPrefixEvent (request, observed))) := by
  cases source with
  | validator bundle raw allocated source =>
    exact ⟨.file allocated.directory.directory.fd "policy.json".toUTF8 raw 384 source⟩
  | @image caller bundle duration allocated source =>
    exact ⟨.image allocated.directory.directory.fd bundle
      (Image.entries (Snapshot.hex allocated.setup.random) bundle.identity
        (caller.command == GatewayWire.checkCommand) caller.fault allocated.setup.policy allocated.setup.frozen) source⟩
  | machine imaged source => exact dispatch_machine imaged source writing
  | @publication caller bundle duration cleaned source => exact publication_file caller bundle cleaned.dispatched.input source writing

end LeanCage.Host.Kernel.WriteSources
