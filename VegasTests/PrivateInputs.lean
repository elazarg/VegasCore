module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.PrivateInputs
public import Vegas.Pending.EventApplication
public import Vegas.Examples.PrivateValueAuction
public import Vegas.Compile.EventGraphAssembly

@[expose] public section

/-! # Private inputs and initial binding resources

Ordinary private valuations require no protocol events or commitment resources.
Initial bindings instead install opaque handles and owner-only candidate meanings.
-/

noncomputable section

namespace VegasTests.PrivateInputs

open Vegas Vegas.SourceProgram GameTheory.Math.Probability Interaction
open Vegas.Examples.PrivateValueAuction
open Vegas.Examples.CommitRevealAuction (Player)

def inputOnly (types : Player → Int) : SourceProgram.Setup
    (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := PMF.pure (initial types)
  obligations := ∅
  program := .ret []
  accounts := rfl
  exitTransfers := fun _ => 0

example : commitmentNames context = ∅ := rfl
example : SourcePublicCtx simpleExpr context = [] := rfl
example (types : Player → Int) : Vegas.eventCount (inputOnly types).program = 0 := rfl

/-- A guard cannot read either private valuation. -/
example (who : Player) (payload : simpleExpr.Ty)
    (read : SourceGuardRead context who payload) : False := by
  cases read with
  | publicData h | commitment h | publication h =>
      cases h with
      | there h => cases h with
        | there h => cases h

example (types : Player → Int) :
    (sourceObserve Player.alice (initial types)).cells.get .here = some (types .alice) := rfl

example (types : Player → Int) :
    (sourceObserve Player.bob (initial types)).cells.get .here = none := rfl

example (types : Player → Int) :
    (sourceObserve Player.bob (initial types)).cells.get (.there .here) = some (types .bob) := rfl

/-- Every source profile retains both ordinary inputs, including after default. -/
example (types : Player → Int) (profile : BehavioralProfile program)
    (terminal : Config Player simpleExpr program.terminalCtx)
    (supported : terminal ∈ (program.run profile (initial types)).support) :
    terminal.state.get (terminalRef program
        (.here : HasVar context 4 (.privateInput .alice .int))) = types .alice ∧
      terminal.state.get (terminalRef program
        (.there .here : HasVar context 5 (.privateInput .bob .int))) = types .bob := by
  have retained := initialState_runFrom program profile (Config.initial (initial types))
    terminal supported
  constructor <;> rw [terminalRef_get, retained] <;> rfl

abbrev graph := Vegas.toEventGraph program
abbrev aliceInput : graph.InputId := ⟨0, by decide⟩
abbrev bobInput : graph.InputId := ⟨1, by decide⟩

def native (types : Player → Int) : EventGraphRuntime.State graph :=
  EventGraphRuntime.State.initial (Vegas.encodeInputs (initial types))

/-- Initial private inputs allocate no accepted commitment handles. -/
example (types : Player → Int) (input : graph.InputId) :
    (native types).accepted (.inl input) = none := by
  fin_cases input <;> rfl

example (types : Player → Int) (who : Player) :
    (native types).candidates.lookup (who, .initial aliceInput) = .fresh := rfl

example (types : Player → Int) (who : Player) :
    (native types).candidates.lookup (who, .initial bobInput) = .fresh := rfl

/-- Native public observations hide valuations; owner observations retain them. -/
example (types : Player → Int) :
    (native types).publicView.observation.store (.inl aliceInput) = none := rfl

example (types : Player → Int) :
    ((native types).playerView .alice).observation.store (.inl aliceInput) =
      some (types .alice) := rfl

example (types : Player → Int) :
    ((native types).playerView .bob).observation.store (.inl aliceInput) = none := rfl

example (types : Player → Int) :
    ((native types).playerView .bob).observation.store (.inl bobInput) =
      some (types .bob) := rfl

/-- Valuations create neither bind events nor dummy resolution events. -/
example : graph.order.eventCount = 4 := rfl

abbrev bindingContext : SourceCtx Player simpleExpr :=
  [(0, .commitment .alice .bool), (1, .commitment .alice .bool)]

def bindingProgram : SourceProgram Player simpleExpr bindingContext {0, 1} :=
  .reveal 2 .alice 0 (by decide) .here (by decide) <|
  .reveal 3 .alice 1 (by decide) (.there (.there .here)) (by decide) <|
  .ret []
abbrev bindingGraph := Vegas.toEventGraph bindingProgram
abbrev openableInput : bindingGraph.InputId := ⟨0, by decide⟩
abbrev unopenableInput : bindingGraph.InputId := ⟨1, by decide⟩

def initialBindings : State simpleExpr bindingContext :=
  Env.cons (.success true) (Env.cons .failure (Env.empty (CellVal simpleExpr)))

def nativeBindings : EventGraphRuntime.State bindingGraph :=
  EventGraphRuntime.State.initial (Vegas.encodeInputs initialBindings)

/-- Both successful and unopenable initial bindings retain canonical handles. -/
example (input : bindingGraph.InputId) :
    nativeBindings.accepted (.inl input) = some (.alice, .initial input) := by
  fin_cases input <;> rfl

example : nativeBindings.candidates.lookup (.alice, .initial openableInput) =
    .openable ⟨.bool, true⟩ := rfl

example : nativeBindings.candidates.lookup (.alice, .initial unopenableInput) = .unopenable := rfl

/-- Another player's slots have no candidate meaning for these bindings. -/
example (input : bindingGraph.InputId) :
    nativeBindings.candidates.lookup (.bob, .initial input) = .fresh := by
  fin_cases input <;> rfl

example (who : Player) (serial : Nat) :
    nativeBindings.candidates.lookup (who, .prepared serial) = .fresh := rfl

example : nativeBindings.bindingResult (.alice, .initial openableInput) .bool = .success true := rfl
example : nativeBindings.bindingResult (.alice, .initial unopenableInput) .bool = .failure := rfl

example (input : bindingGraph.InputId) :
    nativeBindings.publicView.observation.store (.inl input) = none := by
  fin_cases input <;> rfl

example : (nativeBindings.playerView .alice).observation.store (.inl unopenableInput) =
    some PublicationResult.failure := rfl

example (input : bindingGraph.InputId) :
    (nativeBindings.playerView .bob).observation.store (.inl input) = none := by
  fin_cases input <;> rfl

end VegasTests.PrivateInputs
