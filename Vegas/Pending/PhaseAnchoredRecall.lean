/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseEntryOwnRecall
import Interaction.ReactiveAnchoredPolicy

/-! # Anchored raw replay cannot intercept a fresh attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An authentic entry anchor has no recorded input at its new attempt.
Consequently its literal replay follows the continuing policy at every input
of that attempt, including inputs outside the particular anchor extension. -/
theorem phase_anchoredPolicy_of_fresh_attempt
    (anchor : (app).Execution) (players : Player → (app).Policy) (who : Player)
    (attempt : CommitAttemptId)
    (fresh : ∀ record ∈ anchor.recall who,
      record.beforeView.application.2.attempt ≠ attempt)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (address : view.application.2.attempt = attempt) :
    ReactiveApplication.anchoredPolicy anchor players who past view = players who past view := by
  classical
  unfold ReactiveApplication.anchoredPolicy
  cases found : (anchor.recall who)[past.length]? with
  | none => rfl
  | some record =>
    have different : record.beforeView ≠ view := by
      intro same
      exact fresh record (List.mem_of_getElem? found)
        ((congrArg (fun input : (app).PlayerView => input.application.2.attempt)
          same).trans address)
    simp only [different, and_false, ↓reduceIte]

end Vegas.EventGraphRuntime
