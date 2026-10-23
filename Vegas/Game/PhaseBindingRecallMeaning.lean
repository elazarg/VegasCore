/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingRecallWord
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Pending.RecordedBindingReadback
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseSignedBindings
import Vegas.Pending.PhaseNativeProjection
import Vegas.Pending.ReactiveServiceConditions
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Pending.PhaseBindingSubmittedPreservation
import Vegas.Pending.PhaseBindingFreshness
import Interaction.ReactiveRecordedResponse

/-! # Actual private preparations recover their completed source actions

The actual earlier legal callback supplies global freshness. The surviving
accepted handle then identifies the completed graph action with the immutable
preparation in private recall, including an accepted failed binding.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (whole : SourceProgram Player L Γ O) (mode : ExecutionMode)
  (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph whole).withMode mode)))

local notation "app" => phaseApplication runtime leaks

/-- The original menu history derives freshness of every remembered encoded
binding; no current fresh-handle premise is imposed after it has been sent. -/
theorem phaseBindingRecall_fresh (bounds : MessageBounds ((toEventGraph whole).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : ((toEventGraph whole).withMode mode).EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (app).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (declared : entry.action = phaseBindingResponse runtime leaks who event payload result serial) :
    entry.beforeView.application.1.candidates (.prepared serial) = .fresh := by
  obtain ⟨before, prior, _prefix, _acting, viewed, member, _after, _recalled⟩ :=
    (PhaseCount.onePacketMenu runtime leaks bounds).recorded_response_prefix
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler control trace who entry
        retained
  rw [declared] at member
  cases result with
  | failure =>
      exact viewed ▸ PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon
        scheduler prior who event serial none .none member
  | success value =>
      exact viewed ▸ PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon
        scheduler prior who event serial (some ⟨payload, value⟩) .none member

omit [Fintype Player] in
/-- A retained raw entry with this physical address contributes exactly its
decoded effective action to the chronological block word. -/
theorem phaseCommitRecallWord_mem (low high generation : Nat)
    (past : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (retained : entry ∈ past)
    (attempt : entry.beforeView.application.2.attempt = ⟨low, generation⟩)
    (material : WitnessedSubmission ((toEventGraph whole).withMode mode))
    (transmitted : entry.action.transmission = some material)
    (event : ((toEventGraph whole).withMode mode).EventId)
    (candidate : Handle ((toEventGraph whole).withMode mode))
    (named : material.call.packet = .commitment event candidate)
    (inside : low ≤ event.val ∧ event.val < high) (action : OwnAction Player L)
    (decoded : phaseBindingAction? whole mode runtime leaks entry.action = some action) :
    action ∈ phaseCommitRecallWord whole mode runtime leaks low high generation past := by
  apply List.mem_filterMap.mpr
  refine ⟨entry, retained, ?_⟩
  simp only [ite_eq_left attempt, transmitted, named, ite_eq_left inside]
  exact decoded

end Vegas
