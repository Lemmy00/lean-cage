import FilesystemBootstrapSource

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.ownership: The operator approves the selection computed
-- from this actual packet, including a CLI --bundle override. An engine digest
-- or extension default supplies no approval for another selected root.
def callerBootstrapRoot (original : GatewayWire.Request) : Filesystem.Result String :=
  if original.command = GatewayWire.cliCommand then
    match Cli.parse original with
    | .error error => .error error
    | .ok .help => .error "help selects no bootstrap bundle"
    | .ok (.command parsed) => Validation.rootString (parsed.request.field GatewayWire.bundleSlot).bytes
  else
    Validation.rootString (original.field GatewayWire.bundleSlot).bytes

structure OperatorCallerBootstrap {initial : World} (catalogue : BootstrapCatalogue initial)
    (original : GatewayWire.Request) where
  root : String
  selected : callerBootstrapRoot original = .ok root
  authorized : catalogue.roots root

-- §FS-host-boundary.caller: The actual dispatcher, rather than a second argv
-- interpretation, connects operator configuration to the effective request.
def operatorBootstrapSelection {initial : World} {catalogue : BootstrapCatalogue initial}
    {original effective : GatewayWire.Request} {duration : Option Nat}
    (approval : OperatorCallerBootstrap catalogue original)
    (invocation : Commands.Invocation original effective duration) : BootstrapSelection catalogue effective := by
  refine ⟨approval.root, ?_, approval.authorized⟩
  cases invocation with
  | native command => simpa [callerBootstrapRoot, command] using approval.selected
  | cli parsed command parse => simpa [callerBootstrapRoot, command, parse] using approval.selected

def EntryOpening.bootstrapSelection {initial : World} {catalogue : BootstrapCatalogue initial}
    {before : List Program.Event} {operation : Filesystem.Request} {observed : Option Filesystem.Reply}
    (opening : EntryOpening before operation observed)
    (approval : OperatorCallerBootstrap catalogue opening.original) : BootstrapSelection catalogue opening.effective :=
  operatorBootstrapSelection approval opening.invocation

theorem EntryOpening.bootstrapSelection_root {initial : World} {catalogue : BootstrapCatalogue initial}
    {before : List Program.Event} {operation : Filesystem.Request} {observed : Option Filesystem.Reply}
    (opening : EntryOpening before operation observed)
    (approval : OperatorCallerBootstrap catalogue opening.original) :
    (opening.bootstrapSelection approval).root = approval.root := rfl

end LeanCage.Host.Kernel
