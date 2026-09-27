/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingTranscript
import Vegas.Pending.ReactiveBindingOmission

/-! # Public binding allocation excludes missed-binding evidence

The actual accepted-handle invariant identifies the table with the public
completion transcript. Every completed binding in that transcript has an
accepted opaque handle, exactly negating the existing omission detector.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every binding listed in the public allocation transcript has a handle.
The claim also holds for lists with repeated event identifiers. -/
theorem bindingRecords_accepted (inputs : graph.Inputs) (order : List graph.EventId)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (present : event ∈ order) :
    ∃ candidate, (bindingRecords inputs order).2 (.inr event) = some candidate := by
  induction order using List.reverseRecOn with
  | nil => simp only [List.not_mem_nil] at present
  | append_singleton order next ih =>
      rw [bindingRecords_append]
      by_cases same : next = event
      · subst next
        refine ⟨(owner, .prepared ((bindingRecords inputs order).1 owner)), ?_⟩
        change (match graph.outputLayout event with
          | .binding actor _ =>
              (Function.update (bindingRecords inputs order).1 actor
                ((bindingRecords inputs order).1 actor + 1),
                Function.update (bindingRecords inputs order).2 (.inr event)
                  (some (actor, .prepared ((bindingRecords inputs order).1 actor))))
          | .publicData _ | .privateInput _ _ | .publication _ =>
              bindingRecords inputs order).2 (.inr event) = _
        simp only [binding, Function.update_self]
      · have earlier : event ∈ order := by
          rcases List.mem_append.mp present with earlier | last
          · exact earlier
          · exact (same (List.mem_singleton.mp last).symm).elim
        obtain ⟨candidate, accepted⟩ := ih earlier
        refine ⟨candidate, ?_⟩
        change (match graph.outputLayout next with
          | .binding actor _ =>
              (Function.update (bindingRecords inputs order).1 actor
                ((bindingRecords inputs order).1 actor + 1),
                Function.update (bindingRecords inputs order).2 (.inr next)
                  (some (actor, .prepared ((bindingRecords inputs order).1 actor))))
          | .publicData _ | .privateInput _ _ | .publication _ =>
              bindingRecords inputs order).2 (.inr event) = _
        cases graph.outputLayout next with
        | publicData value | privateInput actor value | publication value => exact accepted
        | binding actor value =>
            dsimp only
            rw [Function.update_of_ne (by
              intro equal
              exact same (Sum.inr.inj equal).symm)]
            exact accepted

/-- A state whose accepted handles are given by its public completion order
cannot trigger the existing public missed-binding detector. -/
theorem State.AcceptedRecorded.missedBinding_false {state : State graph}
    (recorded : state.AcceptedRecorded) (event : graph.EventId) :
    state.publicView.missedBinding event = false := by
  cases kind : graph.outputLayout event with
  | publicData payload | privateInput owner payload | publication payload =>
      simp only [PublicView.missedBinding, kind]
  | binding owner payload =>
      by_cases completed : event ∈ (graph.publicObserve state.config).completionOrder
      · obtain ⟨candidate, accepted⟩ := bindingRecords_accepted state.config.inputs
          (graph.publicObserve state.config).completionOrder event owner payload kind completed
        apply state.publicView.missedBinding_of_accepted event candidate
        change state.accepted (.inr event) = some candidate
        rw [recorded]
        exact accepted
      · simp only [PublicView.missedBinding, kind, State.publicView,
          completed, decide_false, Bool.false_and]

end Vegas.EventGraphRuntime
