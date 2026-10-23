/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingShadowStep

/-! # Raw accepted binding completion and its directed private reconstruction -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

/-- Completion changes the repaired field to its original private value only
when the field actually becomes available; unrelated catalogue meanings stay fixed. -/
theorem rememberCompletion_native_complete (memory : BindingShadow graph) (owner : Player)
    (state : State graph) (event : graph.EventId) (ready : state.config.cut.Ready event)
    (originalAction repairedAction : graph.Action event)
    (originalValue repairedValue : (graph.outputLayout event).Value) :
    (memory.rememberCompletion event originalAction originalValue).native owner
        (state.complete event ready repairedAction repairedValue) =
      (memory.native owner state).complete event ready originalAction originalValue := by
  change (⟨_, state.accepted, _, state.clock, _⟩ : State graph) = ⟨_, _, _, _, _⟩
  rw [State.mk.injEq]
  refine ⟨rememberCompletion_config_complete memory state.config event ready
    originalAction repairedAction originalValue repairedValue, rfl, rfl, rfl, rfl⟩

/-- The public accepted handle is shared by the original and repaired meaning. -/
theorem native_setAccepted (memory : BindingShadow graph) (owner : Player)
    (state : State graph) (accepted : AcceptedHandles graph) :
    memory.native owner { state with accepted := accepted } =
      { memory.native owner state with accepted := accepted } := rfl

/-- A single unusable binding is reconstructed with its actual original
catalogue meaning and its original typed failure, including wrong-typed raw data. -/
def failedBinding (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (original : CommitmentCandidate (Raw L)) : BindingShadow graph :=
  ((empty : BindingShadow graph).rememberCandidate (.prepared serial) original).rememberCompletion
    event (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure)
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)

end BindingShadow
end Vegas.EventGraphRuntime
