import FilesystemBoundedContents
import FilesystemInstalledAuthentication

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Installation records initial file bytes and their
-- parsed inventory. It grants no successful loader or later content frame.
structure InstalledBootstrapManifest {initial : World} (catalogue : BootstrapCatalogue initial)
    (root : String) where
  object : ObjectId
  identified : catalogue.files root "manifest.json" object
  raw : ByteArray
  contents : initial.contents object = raw
  manifest : Json.Value
  parsed : Json.parse raw treeMax = .ok manifest

theorem InstalledBootstrapManifest.allocated {initial : World} {catalogue : BootstrapCatalogue initial}
    {root : String} (installed : InstalledBootstrapManifest catalogue root) :
    initial.allocated installed.object = true :=
  catalogue.initialized _ _ _ installed.identified

-- §FS-host-boundary.caller: The real source reads THIS selected manifest and
-- parses those same installed bytes. No hash injectivity is assumed.
theorem actual_loaded_installed_manifest {kernel : Contract} {regular : ObjectId → Prop}
    (reads : PositionedReadContract kernel regular) {origin : FilesystemOrigin}
    {initial : World} {catalogue : BootstrapCatalogue initial} {request : GatewayWire.Request}
    (selection : BootstrapSelection catalogue request)
    (installed : InstalledBootstrapManifest catalogue selection.root)
    (file : regular installed.object) {ordinal : Nat} {before after : World}
    {events : List (Request × Reply)} {bundle : Validation.Bundle}
    (actual : RecordedRun kernel origin ordinal
      (Validation.loadBundle (request.field GatewayWire.bundleSlot).bytes) before events after (.ok bundle))
    (observed : FileReadContentsAt reads.unmodified origin ordinal (ordinal + events.length) installed.object installed.raw) :
    bundle.root = selection.root ∧ bundle.manifest = installed.manifest := by
  obtain ⟨source⟩ := BootstrapProofs.load_bundle_manifest_read _ actual.1
  obtain ⟨middle, reading, _⟩ := recorded_history_split source.reading source.following (source.trace ▸ actual.2)
  have length := congrArg List.length source.trace
  simp only [List.length_append] at length
  have bytes := bounded_read_installed_contents reads file
    (bundle.root ++ "/manifest.json").toUTF8 treeMax ⟨source.copied, reading⟩
    (observed.restrict (by omega) (by omega))
  refine ⟨Except.ok.inj (source.root.symm.trans selection.selected), ?_⟩
  have parsed : Json.parse installed.raw treeMax = .ok bundle.manifest := by
    simpa only [bytes] using source.parsed
  exact Except.ok.inj (parsed.symm.trans installed.parsed)

-- §FS-host-boundary.publication: The fixed installation key is transported to
-- the SAME actual parsed manifest consumed by publication/retrieval consumers.
def installedKeyForLoadedManifest {initial : World} {catalogue : BootstrapCatalogue initial}
    {sha256 : ByteArray → ByteArray} {root : String} (installed : InstalledBootstrapManifest catalogue root)
    (key : InstalledPublicationKey catalogue sha256 root installed.manifest)
    {bundle : Validation.Bundle} (same : bundle.manifest = installed.manifest) :
    InstalledPublicationKey catalogue sha256 root bundle.manifest := same ▸ key

end LeanCage.Host.Kernel
