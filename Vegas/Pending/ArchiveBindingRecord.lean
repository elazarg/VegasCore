/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchivedBindings
import Vegas.Pending.RecordedBindingReadback
import Vegas.Pending.EventValueSwap

/-! # Reading retired binding actions from public handles and private candidates -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PublicView

/-- The owned binding action read from a public accepted handle and the owner's
permanent private candidate catalogue. Nonbinding and foreign events contribute nothing. -/
def bindingRecord? (view : PublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (event : graph.EventId) : Option graph.Completion :=
  match nodeView graph event with
  | .bind owner payload outputEq _ =>
      if owner = who then
        some ⟨event, cast (congrArg EventField.Action outputEq.symm)
          ((view.accepted (.inr event)).elim .failure
            (fun handle => candidateResult (candidates handle.2) payload))⟩
      else none
  | .resolve .. | .sample .. => none

/-- Retired binding choices in their original public completion order. The lower
address removes the saved prefix that is already represented by the effective word. -/
def bindingHistory (view : PublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L)) (low : Nat) :
    List graph.Completion :=
  view.observation.completionOrder.filterMap fun event =>
    if low ≤ event.val then view.bindingRecord? who candidates event else none

/-- A foreign event never contributes an owned binding record. -/
theorem bindingRecord?_eq_none_of_not_actor (view : PublicView graph) (who : Player)
    (candidates : CandidateSlot graph → CommitmentCandidate (Raw L))
    (event : graph.EventId) (notOwned : graph.actor? event ≠ some who) :
    view.bindingRecord? who candidates event = none := by
  cases descriptor : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      have different : owner ≠ who := by
        intro same
        exact notOwned ((graph.actor?_of_outputLayout_binding outputEq).trans
          (congrArg some same))
      simp only [bindingRecord?, descriptor, different, ↓reduceIte]
  | resolve owner payload ref checks outputEq codeEq =>
      simp only [bindingRecord?, descriptor]
  | sample payload law outputEq codeEq => simp only [bindingRecord?, descriptor]

end PublicView

namespace State

/-- An authentic recorded binding can be recovered from its archived public
view and any later permanent own catalogue, including a failed accepted result. -/
theorem BindingInvariant.bindingRecord?_of_recorded {state current : State graph}
    (valid : state.BindingInvariant) {inputs : graph.Inputs}
    (reachable : state.config.Reachable inputs) (fixed : KeepsFixedCandidates state current)
    (event : graph.EventId) (who : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding who payload)
    (action : graph.Action event) (recorded : ⟨event, action⟩ ∈ state.config.history) :
    state.publicView.bindingRecord? who (current.playerView who).candidates event =
      some ⟨event, action⟩ := by
  have read := valid.recorded_binding_action reachable event who payload binding action recorded
  have meaning : (state.accepted (.inr event)).elim .failure
      (fun candidate => state.bindingResult candidate payload) =
      (state.accepted (.inr event)).elim .failure
        (fun candidate => candidateResult ((current.playerView who).candidates candidate.2)
          payload) := by
    cases accepted : state.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        obtain ⟨ty, typed⟩ := valid.accepted_typed (.inr event) candidate accepted
        have owned : candidate.1 = who :=
          (EventField.binding.inj (typed.symm.trans binding)).1
        simp only [Option.elim_some, State.bindingResult_eq]
        rw [← fixed candidate (valid.accepted_fixed (.inr event) candidate accepted)]
        change candidateResult (current.candidates.lookup candidate) payload =
          candidateResult (current.candidates.lookup (who, candidate.2)) payload
        rw [← owned]
  have actual := read.trans meaning
  cases descriptor : nodeView graph event with
  | bind owner ty outputEq codeEq =>
      obtain ⟨rfl, rfl⟩ := EventField.binding.inj (outputEq.symm.trans binding)
      simp only [PublicView.bindingRecord?, descriptor, ↓reduceIte, State.publicView]
      have castActual := congrArg
        (fun value => some (Completion.mk event (cast (congrArg EventField.Action binding.symm)
          value))) actual.symm
      simpa only [cast_cast, cast_eq] using castActual
  | resolve owner ty ref checks outputEq codeEq => cases outputEq.symm.trans binding
  | sample ty law outputEq codeEq => cases outputEq.symm.trans binding

/-- All retired owned binding actions are reconstructible in their actual order
from public completions and the permanent private catalogue. -/
theorem BindingInvariant.bindingHistory_eq {state current : State graph}
    (valid : state.BindingInvariant) {inputs : graph.Inputs}
    (reachable : state.config.Reachable inputs) (fixed : KeepsFixedCandidates state current)
    (who : Player) (low : Nat)
    (bindings : ∀ completion ∈ state.config.history,
      low ≤ completion.event.val → graph.actor? completion.event = some who →
        ∃ payload, graph.outputLayout completion.event = .binding who payload) :
    state.publicView.bindingHistory who (current.playerView who).candidates low =
      graph.ownCompletions who
        (state.config.history.filter fun completion => low ≤ completion.event.val) := by
  change (state.config.history.map Completion.event).filterMap _ = _
  rw [List.filterMap_map]
  have localRead : ∀ completion ∈ state.config.history,
      (if low ≤ completion.event.val then
        state.publicView.bindingRecord? who (current.playerView who).candidates completion.event
      else none) =
      (if low ≤ completion.event.val ∧ graph.actor? completion.event = some who
      then some completion else none) := by
    intro completion member
    by_cases within : low ≤ completion.event.val
    · by_cases owned : graph.actor? completion.event = some who
      · obtain ⟨payload, binding⟩ := bindings completion member within owned
        simp only [within, owned, and_self, ↓reduceIte]
        exact valid.bindingRecord?_of_recorded reachable fixed completion.event who payload
          binding completion.action member
      · simp only [within, owned, and_false, ↓reduceIte]
        exact PublicView.bindingRecord?_eq_none_of_not_actor _ _ _ _ owned
    · simp only [within, false_and, ↓reduceIte]
  simp only [Function.comp_def]
  rw [List.filterMap_congr localRead]
  simp only [EventGraph.ownCompletions, List.filter_filter]
  induction state.config.history with
  | nil => rfl
  | cons completion remaining ih =>
      by_cases within : low ≤ completion.event.val <;>
        by_cases owned : graph.actor? completion.event = some who <;>
        simp [within, owned, ih]

end State

end Vegas.EventGraphRuntime
