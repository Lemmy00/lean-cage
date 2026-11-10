import Lean

open Lean Elab Command

private structure ExpressionArena where
  references : ExprStructMap Nat := {}
  canonical : Std.HashMap String Nat := {}
  nodes : Array Json := #[]

-- §REQ-proof-integrity.statement: Preserve exact kernel terms as a shared, metadata-free DAG.
private partial def expressionNode (expression : Expr) : StateM ExpressionArena Nat := do
  if let some index := (← get).references[(expression : ExprStructEq)]? then return index
  if let .mdata _ inner := expression then
    let index ← expressionNode inner
    modify fun state => { state with references := state.references.insert expression index }
    return index
  let node ← match expression with
    | .app function argument => do
      let function ← expressionNode function
      let argument ← expressionNode argument
      pure <| toJson ("app", [toJson function, toJson argument])
    | .lam name domain body info => do
      let domain ← expressionNode domain
      let body ← expressionNode body
      pure <| toJson ("lam", [toJson (reprStr name), toJson domain, toJson body, toJson (reprStr info)])
    | .forallE name domain body info => do
      let domain ← expressionNode domain
      let body ← expressionNode body
      pure <| toJson ("forall", [toJson (reprStr name), toJson domain, toJson body, toJson (reprStr info)])
    | .letE name type value body nondependent => do
      let type ← expressionNode type
      let value ← expressionNode value
      let body ← expressionNode body
      pure <| toJson ("let", [toJson (reprStr name), toJson type, toJson value, toJson body, toJson nondependent])
    | .proj name index inner => do
      let inner ← expressionNode inner
      pure <| toJson ("proj", [toJson (reprStr name), toJson index, toJson inner])
    | .const name levels => pure <| toJson ("const", [toJson (reprStr name), toJson (reprStr levels)])
    | .sort level => pure <| toJson ("sort", [toJson (reprStr level)])
    | .lit value => pure <| toJson ("literal", [toJson (reprStr value)])
    | .bvar index => pure <| toJson ("bound", [toJson index])
    | .fvar name => pure <| toJson ("free", [toJson (reprStr name)])
    | .mvar name => pure <| toJson ("meta", [toJson (reprStr name)])
    | .mdata _ _ => unreachable!
  let state ← get
  let code := node.compress
  if let some index := state.canonical[code]? then
    set { state with references := state.references.insert expression index }
    return index
  let index := state.nodes.size
  set ({
    references := state.references.insert expression index,
    canonical := state.canonical.insert code index,
    nodes := state.nodes.push node } : ExpressionArena)
  return index

private def expressionDag (expression : Expr) : Json :=
  let (root, arena) := (expressionNode expression).run ({} : ExpressionArena)
  Json.mkObj [("root", toJson root), ("nodes", toJson arena.nodes)]

-- §AR-host-boundary.acceptance: Query actual checked declarations, full types and proof bodies.
private def hostRecord (name : Name) : CommandElabM Json := do
  let declaration ← getConstInfo name
  let axioms ← collectAxioms name
  let type ← liftTermElabM <| withOptions (fun options =>
      options.setBool `pp.all true |>.setBool `pp.universes true |>.setBool `pp.explicit true
        |>.setBool `pp.fullNames true) do
    return (← Meta.ppExpr declaration.type).pretty
  return Json.mkObj [
    ("name", toJson name.toString), ("theorem", toJson declaration.isTheorem),
    ("type", toJson type), ("kernel_type", expressionDag declaration.type),
    ("kernel_body", toJson (declaration.value? true |>.map expressionDag)),
    ("axioms", toJson ((axioms.map Name.toString).qsort (· < ·)))]

private def hostInterface (name : Name) : CommandElabM Unit := do
  logInfo m!"HOST_AUDIT {(← hostRecord name).compress}"
  let constructors := match ← getConstInfo name with
    | .inductInfo info => info.ctors
    | _ => []
  logInfo m!"HOST_AUDIT {(Json.mkObj [("interface", toJson name.toString),
    ("constructors", toJson (constructors.map Name.toString))]).compress}"
  for constructor in constructors do
    logInfo m!"HOST_AUDIT {(Json.mkObj [("interface_parent", toJson name.toString),
      ("declaration", ← hostRecord constructor)]).compress}"

elab "#host_audit_decl " name:ident : command => hostInterface name.getId

-- §REQ-proof-integrity.kernel: Enumerate every theorem in the actual imported source module.
elab "#host_audit_module " moduleName:ident : command => do
  let environment ← getEnv
  unless environment.header.moduleNames.contains moduleName.getId do
    throwError "Module is not imported: {moduleName.getId}"
  let declarations := environment.constants.fold (init := #[]) fun found name info =>
    let fromModule := match environment.getModuleIdxFor? name with
      | none => false
      | some index => environment.header.moduleNames[index]! == moduleName.getId
    if info.isTheorem && fromModule then found.push name else found
  let declarations := declarations.qsort (fun first second => first.toString < second.toString)
  logInfo m!"HOST_AUDIT {(Json.mkObj [("module", toJson moduleName.getId.toString),
    ("declarations", toJson (declarations.map Name.toString))]).compress}"
  for name in declarations do
    logInfo m!"HOST_AUDIT {(← hostRecord name).compress}"
  let interfaces := environment.constants.fold (init := #[]) fun found name info =>
    let fromModule := match environment.getModuleIdxFor? name with
      | none => false
      | some index => environment.header.moduleNames[index]! == moduleName.getId
    match info with
    | .inductInfo _ => if fromModule then found.push name else found
    | _ => found
  let interfaces := interfaces.qsort (fun first second => first.toString < second.toString)
  logInfo m!"HOST_AUDIT {(Json.mkObj [("module_interfaces", toJson moduleName.getId.toString),
    ("interfaces", toJson (interfaces.map Name.toString))]).compress}"
  for name in interfaces do
    hostInterface name
