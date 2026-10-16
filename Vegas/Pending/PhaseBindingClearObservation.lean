/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearHistory
import Vegas.Pending.EventBindingPublicObservation

/-! # Clear phase installation from equal actual external frontiers -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Clean phase advancement reads only the public completed cut. Saved
private meanings and accepted failures do not choose a different descriptor. -/
theorem settle_phases_eq_of_clear (phases : List (RuntimePhase graph))
    (leftGeneration rightGeneration : Nat) (leftEntry rightEntry leftCurrent rightCurrent :
      RecoveryState graph) (leftRetired rightRetired : List (RetiredCommitAttempt graph))
    (publicEq : leftCurrent.native.publicView = rightCurrent.native.publicView)
    (leftClear : leftCurrent.excluded = ∅) (rightClear : rightCurrent.excluded = ∅) :
    (settle phases leftGeneration leftEntry leftCurrent leftRetired).phases =
      (settle phases rightGeneration rightEntry rightCurrent rightRetired).phases := by
  classical
  have cuts := cut_eq_of_completionOrder_eq leftCurrent.native.config rightCurrent.native.config
    (congrArg PublicObservation.completionOrder (congrArg PublicView.observation publicEq))
  induction phases generalizing leftEntry rightEntry with
  | nil => rfl
  | cons phase remaining ih =>
      have leftDrain := phase.drain_eq_of_clear leftCurrent (by
        rintro event ⟨_inside, eligible⟩
        obtain ⟨owner, _acting, excluded⟩ := eligible.owned
        simp only [leftClear, Finset.notMem_empty] at excluded)
      have rightDrain := phase.drain_eq_of_clear rightCurrent (by
        rintro event ⟨_inside, eligible⟩
        obtain ⟨owner, _acting, excluded⟩ := eligible.owned
        simp only [rightClear, Finset.notMem_empty] at excluded)
      have finishedEq : phase.Finished leftCurrent ↔ phase.Finished rightCurrent := by
        unfold RuntimePhase.Finished
        rw [cuts]
      simp only [settle, leftDrain, rightDrain, leftClear, rightClear, Finset.empty_sdiff,
        Finset.empty_inter, Finset.not_nonempty_empty, and_false, ite_false]
      by_cases finished : phase.Finished leftCurrent
      · simp only [finished, finishedEq.mp finished, ite_true]
        exact ih leftCurrent rightCurrent
      · simp only [finished, show ¬phase.Finished rightCurrent from
          fun yes => finished (finishedEq.mpr yes), ite_false]

/-- The actual normalizer preserves equal public views at all clean phase
boundaries, even with unrelated saved private states. -/
theorem normalize_publicView_congr_of_clear (left right : PhaseRuntimeState graph)
    (phases : left.phases = right.phases) (generation : left.generation = right.generation)
    (retired : left.retired.map (fun prior => (prior.attempt, prior.state.publicView)) =
      right.retired.map (fun prior => (prior.attempt, prior.state.publicView)))
    (publicEq : left.current.native.publicView = right.current.native.publicView)
    (leftClear : left.current.excluded = ∅) (rightClear : right.current.excluded = ∅) :
    left.normalize.publicView = right.normalize.publicView := by
  have first := settle_of_clear left.phases left.generation left.entry left.current left.retired
    leftClear
  have second := settle_of_clear right.phases right.generation right.entry right.current
    right.retired rightClear
  have selected : left.normalize.phases = right.normalize.phases := by
    unfold normalize
    rw [phases]
    exact settle_phases_eq_of_clear _ _ _ _ _ _ _ _ _ publicEq leftClear rightClear
  simp only [publicView, attempt, show left.normalize.current = left.current from first.1,
    show right.normalize.current = right.current from second.1,
    show left.normalize.generation = left.generation from first.2.1,
    show right.normalize.generation = right.generation from second.2.1,
    show left.normalize.retired = left.retired from first.2.2,
    show right.normalize.retired = right.retired from second.2.2,
    selected, generation, retired, leftClear, rightClear, publicEq]

end Vegas.EventGraphRuntime.PhaseRuntimeState
