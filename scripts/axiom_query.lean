import Lean
import LeanCage

-- §AR-filter-decoder.audit: Inspect actual checked declarations and their transitive axioms.
open Lean Elab Command

private def declarationRecord (name : Name) : CommandElabM Json := do
  let info ← getConstInfo name
  let axioms ← collectAxioms name
  let type ← liftTermElabM <| withOptions
    (fun options => options.setBool `pp.fullNames true |>.setBool `pp.universes true) do
      return (← Meta.ppExpr info.type).pretty
  return Json.mkObj [
    ("name", toJson name.toString),
    ("type", toJson type),
    ("is_theorem", toJson info.isTheorem),
    ("axioms", toJson (axioms.map Name.toString))]

elab "#audit_decl " name:ident : command => do
  logInfo m!"LEANCAGE_AUDIT {(← declarationRecord name.getId).compress}"

-- §AR-filter-decoder.audit: Enumerating project modules prevents an omitted theorem passing.
elab "#audit_module " moduleName:ident : command => do
  let env ← getEnv
  if !env.header.moduleNames.contains moduleName.getId then
    throwError "Module is not imported: {moduleName.getId}"
  let names := env.constants.fold (init := #[]) fun names name info =>
    let fromModule := match env.getModuleIdxFor? name with
      | none => false
      | some index => env.header.moduleNames[index]! == moduleName.getId
    if info.isTheorem && fromModule then names.push name else names
  let inventory := Json.mkObj [
    ("module", toJson moduleName.getId.toString),
    ("declarations", toJson (names.map Name.toString))]
  logInfo m!"LEANCAGE_AUDIT {inventory.compress}"
  for name in names do
    logInfo m!"LEANCAGE_AUDIT {(← declarationRecord name).compress}"
