/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/
import Lean

open Lean Elab

/-- State of the separate paper validator; it is never imported by the paper. -/
structure PaperAudit where
  seen : NameSet := {}
  notations : Array (String × Nat) := #[]
  results : NameSet := {}
  pins : NameSet := {}
  pending : Option Name := none
  errors : Array String := #[]

/-- Machine-readable result of parsing and elaborating a paper file. -/
structure PaperAudit.Report where
  file : String
  results : Array String
  pins : Array String
  errors : Array String
  deriving ToJson

/-- The parser and command states needed for a standalone audit. -/
private structure PaperAudit.Input where
  commandState : Command.State
  parserState : Parser.ModuleParserState
  cmdPos : String.Pos.Raw

private abbrev PaperAudit.Elaboration := ReaderT Parser.InputContext (StateRefT PaperAudit.Input IO)

private def PaperAudit.runCommandElabM {α : Type} (action : Command.CommandElabM α) :
    PaperAudit.Elaboration α := do
  let ctx ← read
  let state ← get
  let context : Command.Context := {
    cmdPos := state.cmdPos, fileName := ctx.fileName, fileMap := ctx.fileMap,
    snap? := none, cancelTk? := none }
  match ← EIO.toIO' <| (action context).run state.commandState with
  | .error error => throw <| IO.userError (← error.toMessageData.toString)
  | .ok (value, commands) =>
    modify fun s => { s with commandState := commands }
    return value

private def PaperAudit.fail (state : IO.Ref PaperAudit) (message : String) :
    PaperAudit.Elaboration Unit :=
  state.modify fun s => { s with errors := s.errors.push message }

private partial def PaperAudit.identifiers (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId]
  else stx.getArgs.foldl (fun names child => names ++ identifiers child) #[]

private def PaperAudit.checkNotationName (token : String) : Command.CommandElabM Unit := do
  let name := token.toName
  let scope := (← get).scopes.head!
  let resolved := Lean.ResolveName.resolveGlobalName (← getEnv) scope.opts
    scope.currNamespace scope.openDecls name
  unless resolved.isEmpty do
    throwError "Paper notation shadows an existing name: {token}"
  if scope.varDecls.any (fun vars => (identifiers vars).contains name) then
    throwError "Paper notation shadows a section variable: {token}"

/-- Permit opens only in the domain namespaces used to state paper concepts. -/
private def PaperAudit.checkOpen (tokens : Array String) (decl : Syntax) :
    Command.CommandElabM Unit := do
  unless decl.isOfKind ``Parser.Command.openSimple do
    throwError "only ordinary namespace opens are allowed in Paper"
  for name in identifiers decl do
    let namespaces ← resolveNamespaceCore name
    unless !namespaces.isEmpty && namespaces.all (fun ns =>
        #[`Vegas, `GameTheory, `Interaction].any (·.isPrefixOf ns)) do
      throwError "Paper opens only Vegas, GameTheory and Interaction namespaces: {name}"
  let opened ← elabOpenDecl ⟨decl⟩
  Command.withScope (fun scope => { scope with openDecls := opened }) do
    for token in tokens do checkNotationName token

private partial def PaperAudit.checkTermOpens (tokens : Array String) (stx : Syntax) :
    Command.CommandElabM Unit := do
  if stx.isOfKind ``Parser.Term.«open» || stx.isOfKind ``Parser.Tactic.«open» then
    checkOpen tokens stx[1]
  for child in stx.getArgs do checkTermOpens tokens child

/-- Validate actual parser nodes before the command can change the environment. -/
private partial def PaperAudit.command (tokens : Array String) (cmd : Syntax) :
    Command.CommandElabM (Option Syntax) := do
  let kind := cmd.getKind
  checkTermOpens tokens cmd
  if (cmd.find? fun node => node.isOfKind ``Parser.Term.whereDecls ||
      node.isOfKind ``Parser.Term.letrec || node.isOfKind ``Parser.Term.letRecDecl).isSome then
    throwError "Paper declarations cannot use where or let rec helpers"
  if (cmd.find? (·.isOfKind ``Parser.Term.attributes)).isSome then
    throwError "Paper commands cannot install attributes or instances"
  if kind == ``Parser.Command.in then
    unless #[``Parser.Command.include, ``Parser.Command.omit, ``Parser.Command.variable,
        ``Parser.Command.open].contains cmd[0].getKind do
      throwError "unsupported scoped Paper command"
    let _ ← command tokens cmd[0]
    return ← command tokens cmd[2]
  if kind == ``Parser.Command.declaration then
    unless cmd[0].getArgs.toList.drop 1 |>.all (·.isNone) do
      throwError "Paper declarations cannot install attributes, instances or modifiers"
    let decl := cmd[1]
    unless #[``Parser.Command.definition, ``Parser.Command.abbrev,
        ``Parser.Command.theorem, ``Parser.Command.structure].contains decl.getKind do
      throwError "unsupported Paper declaration kind: {decl.getKind}"
    -- Deriving clauses have several parser wrappers; inspect their actual atom.
    if (decl.find? fun node => node.isAtom && node.getAtomVal == "deriving").isSome then
      throwError "Paper declarations cannot derive instances"
    if decl.isOfKind ``Parser.Command.structure && decl[0].isOfKind ``Parser.Command.classTk then
      throwError "Paper declarations cannot create classes"
    let name := decl[1][0].getId
    unless (`Vegas.Paper).isPrefixOf name && name != `Vegas.Paper do
      throwError "use a fully qualified Paper declaration name: {name}"
    return some decl
  if kind == ``Parser.Command.open then
    checkOpen tokens cmd[1]
    return none
  if kind == ``Parser.Command.notation then
    unless cmd[0].isNone && cmd[1].isNone &&
        (cmd[2].find? (·.isOfKind ``Parser.Term.local)).isSome &&
        cmd[4].isNone && cmd[5].isNone && cmd[6].isNone && cmd[7].getArgs.size == 1 do
      throwError "Paper permits only a fresh local identifier shorthand"
    let some token := cmd[7][0].isStrLit? | throwError "expected a local identifier shorthand"
    unless !token.isEmpty && isIdFirst token.toList.head! && token.toList.all isIdRest do
      throwError "Paper notation must be a fresh identifier"
    if ((Parser.getTokenTable (← getEnv)).find? token).isSome then
      throwError "Paper notation shadows a parser token: {token}"
    checkNotationName token
    return none
  if #[``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
      ``Parser.Command.variable, ``Parser.Command.include, ``Parser.Command.omit,
      ``Parser.Command.moduleDoc].contains kind then
    return none
  throwError "unsupported Paper command kind: {kind}"

private def PaperAudit.guardTarget (cmd : Syntax) : Command.CommandElabM Name := do
  match cmd with
  | `(command| $[$doc?:docComment]? #guard_msgs (whitespace := lax) in $child) =>
    unless doc?.isSome do throwError "axiom guard needs its expected message"
    unless child.raw.isOfKind ``Parser.Command.printAxioms do
      throwError "Paper guards must check only an axiom print"
    return child.raw[2].getId
  | _ => throwError "axiom pin requires exactly #guard_msgs (whitespace := lax)"

/-- The coverage check is separate from adjacency, so both are tested independently. -/
private def PaperAudit.missingPinErrors (state : PaperAudit) : Array String :=
  state.results.toArray.filterMap fun name =>
    if state.pins.contains name then none else some s!"missing guarded axiom pin for {name}"

private def PaperAudit.checkAdjacency (state : IO.Ref PaperAudit)
    (pending target : Option Name) : PaperAudit.Elaboration Unit := do
  unless pending == target do
    PaperAudit.fail state "exact axiom pin must immediately follow its result"

private def PaperAudit.binderType? (binder : Syntax) : Option Syntax :=
  if binder.isOfKind ``Parser.Term.instBinder then some binder[2]
  else if #[``Parser.Term.explicitBinder, ``Parser.Term.implicitBinder,
      ``Parser.Term.strictImplicitBinder].contains binder.getKind &&
      binder[2].getArgs.size == 2 then some binder[2][1]
  else none

private partial def PaperAudit.typeHasHole (stx : Syntax) : Bool := Id.run do
  if let some type := binderType? stx then return typeHasHole type
  if stx.isOfKind ``Parser.Term.basicFun then
    for binder in stx[0].getArgs do
      let type? := if let some type := binderType? binder then some type
        else match binder with
          | `(term| ($_name : $type)) => some type.raw
          | _ => none
      if type?.any typeHasHole then return true
    return stx.getArgs.toList.drop 1 |>.any typeHasHole
  return stx.isOfKind ``Parser.Term.hole || stx.getArgs.any typeHasHole

private def PaperAudit.checkExplicitStatement (state : IO.Ref PaperAudit)
    (decl : Syntax) (name : Name) : PaperAudit.Elaboration Unit := do
  let resultType := decl[2][1]
  let type? := if resultType.isOfKind ``Parser.Term.typeSpec then some resultType
    else resultType.getArgs.find? (·.isOfKind ``Parser.Term.typeSpec)
  unless type?.isSome do
    PaperAudit.fail state s!"{name} needs its full explicit statement"
  for binder in decl[2][0].getArgs do
    unless (binderType? binder).any (fun type => !typeHasHole type) do
      PaperAudit.fail state s!"{name} needs explicit binder types"


private def PaperAudit.collectMessages (state : IO.Ref PaperAudit) :
    PaperAudit.Elaboration Unit := do
  let after := (← get).commandState
  let messages := after.messages ++ after.snapshotTasks.foldl
    (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) .empty) .empty
  modify fun s => { s with commandState := { after with messages := {}, snapshotTasks := #[] } }
  for msg in messages.toList do
    if msg.severity == .error then
      let text ← msg.toString
      state.modify fun s => { s with errors := s.errors.push ("Lean elaboration: " ++ text) }

/-- Policy rejections are ordinary audit diagnostics, not frontend internal exceptions. -/
private def PaperAudit.attempt {α : Type} (action : Command.CommandElabM α) :
    PaperAudit.Elaboration (Except String α) :=
  runCommandElabM do
    try return .ok (← action)
    catch error => return .error (← error.toMessageData.toString)

private partial def PaperAudit.loop (state : IO.Ref PaperAudit) : PaperAudit.Elaboration Unit := do
  modify fun s => { s with cmdPos := s.parserState.pos }
  let before := (← get).commandState
  let ctx ← read
  let scope := before.scopes.head!
  let (cmd, ps, messages) := Parser.parseCommand ctx
    { env := before.env, options := scope.opts, currNamespace := scope.currNamespace,
      openDecls := scope.openDecls } (← get).parserState {}
  modify fun s => { s with parserState := ps }
  if messages.hasErrors then
    for msg in messages.toList do
      let text ← msg.toString
      state.modify fun s => { s with errors := s.errors.push ("Lean parser: " ++ text) }
    return
  if Parser.isTerminalCommand cmd then
    unless cmd.isOfKind ``Parser.Command.eoi do
      PaperAudit.fail state s!"unsupported terminal Paper command: {cmd.getKind}"
    return
  let pin := cmd.isOfKind ``Lean.guardMsgsCmd
  let pending := (← state.get).pending
  let tokens := (← state.get).notations.map Prod.fst
  let checked : Except String (Sum Name (Option Syntax)) ←
    attempt (if pin then return .inl (← guardTarget cmd)
      else return .inr (← command tokens cmd))
  let .ok validated := checked | do
    let .error message := checked | return
    PaperAudit.fail state message
    loop state
    return
  let primary? ← match validated with
    | .inl target => do
      let audit ← state.get
      unless audit.results.contains target do
        PaperAudit.fail state s!"axiom pin names no local result: {target}"
      checkAdjacency state pending (some target)
      if audit.pins.contains target then PaperAudit.fail state s!"duplicate axiom pin for {target}"
      state.modify fun s => { s with pins := s.pins.insert target, pending := none }
      if audit.results.contains target then
        let dependencies ← runCommandElabM (collectAxioms target)
        for name in dependencies do
          unless #[`propext, `Classical.choice, `Quot.sound].contains name do
            PaperAudit.fail state s!"nonstandard axiom in {target}: {name}"
      pure none
    | .inr decl => do
      checkAdjacency state pending none
      state.modify fun s => { s with pending := none }
      pure decl
  runCommandElabM <| withRef cmd <| Command.elabCommand cmd
  collectMessages state
  let after := (← get).commandState
  state.modify fun s =>
    { s with notations := s.notations.filter (fun entry => entry.2 ≤ after.scopes.length) }
  if cmd.isOfKind ``Parser.Command.notation then
    if let some token := cmd[7][0].isStrLit? then
      state.modify fun s => { s with notations := s.notations.push (token, after.scopes.length) }
  for (token, _) in (← state.get).notations do
    if let .error message ← attempt (checkNotationName token) then
      PaperAudit.fail state message
  if let some decl := primary? then
    if decl.isOfKind ``Parser.Command.structure then
      let name := decl[1][0].getId
      for field in getStructureFieldsFlattened after.env name do
        if (getDefaultFnForField? after.env name field).isSome ||
            (getAutoParamFnForField? after.env name field).isSome then
          let some owner := findField? after.env name field | continue
          let some projection := getProjFnForField? after.env owner field | continue
          let some info := after.env.find? projection | continue
          let prop ← runCommandElabM <| Command.liftTermElabM <| Meta.isProp info.type
          if prop then
            PaperAudit.fail state
              s!"proof-valued structure default must be a separate named result: {projection}"
  let locals ← after.env.getLocalConstantInfos
  for info in locals do
    unless (← state.get).seen.contains info.name do
      state.modify fun s => { s with seen := s.seen.insert info.name }
      if primary?.any (fun decl => decl[1][0].getId == info.name) then
        let prop ← runCommandElabM <| Command.liftTermElabM <| Meta.isProp info.toConstantVal.type
        if prop then
          let decl := primary?.get!
          checkExplicitStatement state decl info.name
          state.modify fun s =>
            { s with results := s.results.insert info.name, pending := some info.name }
  loop state

/-- Audit a file in a separately loaded import environment, without loader trust overrides. -/
def PaperAudit.run (env : Environment) (opts : Options) (file : String) : IO PaperAudit.Report := do
  let inputCtx := Parser.mkInputContext (← IO.FS.readFile file) file
  let (_, ps, messages) ← Parser.parseHeader inputCtx
  let seen := (← env.getLocalConstantInfos).foldl (fun names info => names.insert info.name)
    ({} : NameSet)
  let state ← IO.mkRef ({ seen } : PaperAudit)
  for msg in messages.toList do
    if msg.severity == .error then
      let text ← msg.toString
      state.modify fun s => { s with errors := s.errors.push ("Lean header: " ++ text) }
  if !messages.hasErrors then
    let _ ← ((loop state).run inputCtx).run {
      commandState := Command.mkState
        (env.setMainModule (.str .anonymous s!"PaperAuditInput_{hash file}")) {} opts
      parserState := ps, cmdPos := ps.pos }
  let result ← state.get
  let errors := result.errors ++ result.missingPinErrors
  let errors := if result.results.isEmpty && errors.isEmpty then
    errors.push "Paper must contain stated results and pins" else errors
  return {
    file := file
    results := result.results.toArray.map toString
    pins := result.pins.toArray.map toString
    errors := errors
  }

/-- Parse import headers with Lean, for the separate audit driver. -/
def main (args : List String) : IO UInt32 := do
  let mut result : Array Json := #[]
  for file in args do
    let ctx := Parser.mkInputContext (← IO.FS.readFile file) file
    let (_, ps, messages) ← Parser.parseHeader ctx
    if messages.hasErrors then throw <| IO.userError s!"invalid import header: {file}"
    result := result.push <| Json.mkObj
      [("file", toJson file), ("headerEnd", toJson ps.pos.byteIdx)]
  IO.println (toJson result).compress
  return 0
