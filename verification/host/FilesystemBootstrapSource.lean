import BootstrapProofs
import FilesystemBootstrapOpens
import FilesystemSourceOrigins
import FilesystemPrimitiveRecording

namespace LeanCage.Host.Kernel
open Filesystem

theorem selected_bundle_loaded {request : GatewayWire.Request} (source : CallerPrefixCuts.Selected request) :
    BootstrapProofs.Loaded (request.field GatewayWire.bundleSlot).bytes source.bundle :=
  BootstrapProofs.load_bundle_source _ source.select

-- §FS-host-boundary.caller: This original manifest call is justified at its actual
-- prefix, including a lost reply, before any successful loadBundle result exists.
theorem bootstrap_manifest_source {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem
      (Validation.loadBundle (request.field GatewayWire.bundleSlot).bytes))
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (BootstrapReadSource catalogue request operation) := by
  obtain ⟨root, decoded, exactCall⟩ := selected_filesystem_profile (BootstrapProofs.load_bundle_opens _) source opening
  have same : root = selection.root := Except.ok.inj (decoded.symm.trans selection.selected)
  subst root
  exact ⟨⟨selection, "manifest.json", BootstrapProofs.manifest_canonical, by
    simpa only [String.append_assoc, show "/" ++ "manifest.json" = "/manifest.json" by rfl] using exactCall⟩⟩

theorem bootstrap_loaded_source {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    (selected : CallerPrefixCuts.Selected request) {α : Type} {program : Filesystem.Program α}
    (profile : RequestProgram (BootstrapProofs.BundleOpen selected.bundle.root) program)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem program)
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (BootstrapReadSource catalogue request operation) := by
  have loaded := selected_bundle_loaded selected
  have same : selected.bundle.root = selection.root := Except.ok.inj (loaded.root.symm.trans selection.selected)
  obtain ⟨name, canonical, exactCall⟩ := selected_filesystem_profile profile source opening
  exact ⟨⟨selection, name, canonical, by simpa only [same] using exactCall⟩⟩

theorem bootstrap_component_source {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    (selected : CallerPrefixCuts.Selected request) (name : String) (limit : Nat)
    (canonical : Validation.canonicalName name = true)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem (Validation.copyIdentified selected.bundle name limit))
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (BootstrapReadSource catalogue request operation) :=
  bootstrap_loaded_source selection selected (BootstrapProofs.identified_opens _ _ _ canonical) source opening

theorem bootstrap_check_file_source {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    (selected : CallerPrefixCuts.Selected request) (name : String) (limit : Nat)
    (canonical : Validation.canonicalName name = true)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem (Validation.checkFile selected.bundle name limit))
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (BootstrapReadSource catalogue request operation) :=
  bootstrap_loaded_source selection selected (BootstrapProofs.checked_file_opens _ _ _ canonical) source opening

theorem bootstrap_inventory_source {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    (selected : CallerPrefixCuts.Selected request)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem (Validation.checkBundle selected.bundle))
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (BootstrapReadSource catalogue request operation) :=
  bootstrap_loaded_source selection selected
    (BootstrapProofs.checked_bundle_opens (selected_bundle_loaded selected)) source opening

theorem bootstrap_key_source {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request)
    (selected : CallerPrefixCuts.Selected request)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem (Publication.authenticationKey selected.bundle))
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (BootstrapReadSource catalogue request operation) :=
  bootstrap_loaded_source selection selected
    (BootstrapProofs.authentication_key_opens (selected_bundle_loaded selected)) source opening

inductive CallerOpening {initial : World} (catalogue : BootstrapCatalogue initial)
    (request : GatewayWire.Request) (duration : Option Nat) (before : List Program.Event)
    (operation : Request) (observed : Option Reply) : Type 1 where
  | bootstrap (source : BootstrapReadSource catalogue request operation)
  | loadingPolicy (context : CallerPrefixCuts.Authenticated request) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (Validation.loadPolicy request))
        (inside ++ [Program.filesystemPrefixEvent (operation, observed)]))
      (trace : before = context.events ++ inside)
  | validating (context : CallerPrefixCuts.Authenticated request) (raw : ByteArray)
      (loading : List (Request × Reply))
      (load : Returns (Validation.loadPolicy request) loading (.ok raw)) (inside : List Program.Event)
      (active : Program.Prefix (Validation.validateCopied context.bundle raw)
        (inside ++ [Program.filesystemPrefixEvent (operation, observed)]))
      (trace : before = context.events ++ loading.map Program.filesystemEvent ++ inside)
  | executing (context : CallerPrefixCuts.Authenticated request) (inside : List Program.Event)
      (command : request.command = GatewayWire.runCommand ∨ request.command = GatewayWire.checkCommand)
      (active : Program.Prefix (executeRun request context.bundle duration).run
        (inside ++ [Program.filesystemPrefixEvent (operation, observed)]))
      (trace : before = context.events ++ inside)
  | retrieving (context : CallerPrefixCuts.Authenticated request) (inside : List Program.Event)
      (command : request.command = GatewayWire.reportCommand)
      (active : Program.Prefix (Program.liftFilesystem (Retrieval.report request context.bundle))
        (inside ++ [Program.filesystemPrefixEvent (operation, observed)]))
      (trace : before = context.events ++ inside)

-- §FS-host-boundary.caller: The bootstrap roles come from real caller phase cuts.
-- Every remaining open retains the exact authenticated continuation for its own source proof.
theorem caller_opening_source {initial : World} {catalogue : BootstrapCatalogue initial}
    {request : GatewayWire.Request} (selection : BootstrapSelection catalogue request) (duration : Option Nat)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix (execute request duration)
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (CallerOpening catalogue request duration before operation observed) := by
  obtain ⟨cut⟩ := CallerPrefixCuts.execute_checked_cut request duration source
  cases cut with
  | selecting active =>
    obtain ⟨actual⟩ := bootstrap_manifest_source selection active opening
    exact ⟨.bootstrap actual⟩
  | checking context inside active trace =>
    obtain ⟨actual⟩ := bootstrap_inventory_source selection context active opening
    exact ⟨.bootstrap actual⟩
  | identifying context inside active trace =>
    exact False.elim (selected_filesystem_profile (BootstrapProofs.engine_identity_no_open _) active opening)
  | authenticating context inside active trace =>
    obtain ⟨actual⟩ := bootstrap_loaded_source selection context.checked.selected
      (BootstrapProofs.key_gate_opens (selected_bundle_loaded context.checked.selected)) active opening
    exact ⟨.bootstrap actual⟩
  | loadingPolicy context inside active trace => exact ⟨.loadingPolicy context inside active trace⟩
  | validating context raw loading load inside active trace =>
    exact ⟨.validating context raw loading load inside active trace⟩
  | executing context inside command active trace => exact ⟨.executing context inside command active trace⟩
  | retrieving context inside command active trace => exact ⟨.retrieving context inside command active trace⟩

structure EntryOpening (before : List Program.Event) (operation : Request) (observed : Option Reply) where
  packet : EntrypointPrefixCuts.Read
  original : GatewayWire.Request
  effective : GatewayWire.Request
  duration : Option Nat
  accepted : packet.packet = .ok original
  invocation : Commands.Invocation original effective duration
  inside : List Program.Event
  active : Program.Prefix (execute effective duration)
    (inside ++ [Program.filesystemPrefixEvent (operation, observed)])
  trace : before = packet.events ++ inside

-- §FS-host-boundary.caller: Bundle authority must attach to THIS derived effective
-- request, including the real CLI parser result, rather than to a default root.
theorem entrypoint_opening_source {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (opening : operation.op = .openAt) : Nonempty (EntryOpening before operation observed) := by
  obtain ⟨cut⟩ := EntrypointPrefixCuts.entrypoint_cut source
  cases cut with
  | starting active =>
    exact False.elim (selected_filesystem_profile (BootstrapProofs.startup_no_open [0, 1, 3]) active opening)
  | reading context inside active trace =>
    exact False.elim (selected_filesystem_profile (BootstrapProofs.packet_no_open _) active opening)
  | responding context inside active trace =>
    obtain ⟨original, packet, called⟩ := EntrypointPrefixCuts.packet_response_prefix active
    obtain ⟨effective, duration, invocation, executed⟩ := Commands.run_prefix_source original called
    exact ⟨⟨context, original, effective, duration, packet, invocation, inside, executed, trace⟩⟩
  | writing context inside bound active trace =>
    exact False.elim (selected_filesystem_profile (BootstrapProofs.write_loop_no_open _ _ _ _) active opening)

-- §AR-host-boundary.primitives: Extra read-only guard operations do not invent an
-- open role. This raw open is the primary call of the SAME actual source occurrence.
theorem primitive_entry_opening_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {operation : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine operation observed)
    (opening : operation.op = .openAt) :
    Nonempty (EntryOpening adapter.occurrence.logicalBefore operation none) := by
  have same := PrimitiveFilesystem.filesystem_occurrence_primary adapter.occurrence
    (by rw [opening]; decide) (by rw [opening]; decide) (by rw [opening]; decide)
  have source := PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  rw [← same] at source
  exact entrypoint_opening_source source opening

end LeanCage.Host.Kernel
