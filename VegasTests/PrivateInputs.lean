/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.PrivateInputs
import Vegas.Pending.PrivateInputs
import Vegas.Examples.PrivateValueAuction

/-! # Private valuations require no protocol actions

The same two-input context is used at source, graph, and native levels. These
checks cover access restrictions and the absence of commitment resources.
-/

noncomputable section

namespace VegasTests.PrivateInputs

open Vegas Vegas.SourceProgram GameTheory.Math.Probability Interaction
open Vegas.Examples.PrivateValueAuction
open Vegas.Examples.CommitRevealAuction (Player)

/-- Returning immediately with private inputs is a checked source program. -/
private def inputOnly (types : Player → Int) : SourceProgram.Initial
    (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  state := initial types
  obligations := ∅
  program := .ret []
  accounts := rfl

example : commitmentNames context = ∅ := rfl
example : SourcePublicCtx simpleExpr context = [] := rfl
example (types : Player → Int) : EventLowering.eventCount (inputOnly types).program = 0 := rfl

/-- There is no guard operand that reads either private valuation. -/
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

private abbrev graph := EventLowering.toEventGraph program
private abbrev aliceInput : graph.InputId := ⟨0, by decide⟩
private abbrev bobInput : graph.InputId := ⟨1, by decide⟩

private def native (types : Player → Int) : EventGraphRuntime.State graph :=
  EventGraphRuntime.State.initial (EventLowering.encodeInputs (initial types))

/-- Initial private inputs allocate no accepted commitment handles. -/
example (types : Player → Int) (input : graph.InputId) :
    (native types).accepted (.inl input) = none := by
  fin_cases input <;> rfl

example (types : Player → Int) (who : Player) :
    (native types).candidates.lookup (who, .initial aliceInput) = .fresh :=
  EventGraphRuntime.State.initial_privateInput_candidate _ aliceInput .alice who .int rfl

example (types : Player → Int) (who : Player) :
    (native types).candidates.lookup (who, .initial bobInput) = .fresh :=
  EventGraphRuntime.State.initial_privateInput_candidate _ bobInput .bob who .int rfl

/-- Native public observations hide valuations; owner observations retain them. -/
example (types : Player → Int) :
    (native types).publicView.observation.store (.inl aliceInput) = none := rfl

example (types : Player → Int) :
    ((native types).playerView .alice).observation.store (.inl aliceInput) =
      some (types .alice) := rfl

example (types : Player → Int) :
    ((native types).playerView .bob).observation.store (.inl aliceInput) = none := rfl

/-- Valuations create neither bind events nor dummy resolution events. -/
example : graph.order.eventCount = 4 := rfl

end VegasTests.PrivateInputs
