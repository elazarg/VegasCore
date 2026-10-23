/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnusableBinding

/-! # Public allocation of canonical commitment handles

At a clean protected prefix, the next prepared serial is the number of this
owner's completed bindings. Both valid and unusable private material consume
exactly one serial. The auditor reads the public completion list; it does not
inspect a private candidate catalog.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def PublicView.bindingCount (view : PublicView graph) (who : Player) : Nat :=
  view.observation.completionOrder.countP fun event =>
    match graph.outputLayout event with
    | .binding owner _ => decide (owner = who)
    | .publicData _ | .privateInput _ _ | .publication _ => false

def State.PreparedPrefix (state : State graph) (who : Player) : Prop :=
  ∀ serial, state.candidates.lookup (who, .prepared serial) = .fresh ↔
    state.publicView.bindingCount who ≤ serial

theorem State.preparedPrefix_initial (inputs : graph.Inputs) (who : Player) :
    (State.initial inputs).PreparedPrefix who := by
  intro serial
  rw [State.initial_candidate]
  simp [PublicView.bindingCount, State.publicView, State.initial,
    EventGraph.publicObserve, EventGraph.Config.initial]

theorem State.PreparedPrefix.freshSlot {state : State graph} {who : Player}
    (prefixFresh : state.PreparedPrefix who)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    reactiveFreshSlot ((runtime.reactiveApplication leaks).observePlayer state who) =
      some (state.publicView.bindingCount who) := by
  classical
  have existsFresh : ∃ serial, state.candidates.lookup (who, .prepared serial) = .fresh :=
    ⟨state.publicView.bindingCount who, (prefixFresh _).mpr (Nat.le_refl _)⟩
  unfold reactiveFreshSlot
  change (if fresh : ∃ serial,
      state.candidates.lookup (who, .prepared serial) = .fresh then
    some (Nat.find fresh) else none) = _
  rw [dite_eq_left existsFresh]
  apply congrArg some
  apply Nat.le_antisymm
  · exact Nat.find_min' existsFresh ((prefixFresh _).mpr (Nat.le_refl _))
  · exact (prefixFresh _).mp (Nat.find_spec existsFresh)

theorem State.bindingCount_complete (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) (owner who : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) :
    (state.complete event ready action value).publicView.bindingCount who =
      state.publicView.bindingCount who + if owner = who then 1 else 0 := by
  simp [PublicView.bindingCount, State.publicView, State.complete, EventGraph.publicObserve,
    binding]

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem submitted_binding_fresh_iff
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (query : CandidateSlot graph) :
    let response : (runtime.reactiveApplication leaks).Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩
    let submitted := execution.respond (runtime.reactiveApplication leaks) who response
    submitted.application.candidates.lookup (who, query) = .fresh ↔
      query ≠ .prepared serial ∧
        execution.application.candidates.lookup (who, query) = .fresh := by
  let material : Submission graph := ⟨.commitment event (who, .prepared serial), opening⟩
  change (submitStep (material.register execution.application who) who
    material.packet).candidates.lookup (who, query) = .fresh ↔ _
  rw [material.candidateAfter_eq]
  by_cases selected : query = .prepared serial
  · subst query
    cases fixed : execution.application.candidates.lookup (who, .prepared serial) <;>
      cases opening <;> simp [material, Submission.candidateAfter, fixed]
  · simp [material, Submission.candidateAfter, selected]

end Vegas.EventGraphRuntime
