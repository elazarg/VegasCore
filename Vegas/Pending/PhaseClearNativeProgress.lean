/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseReactiveValueSwap

/-! # Native semantic preservation through all clear phase transitions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Native acceptance only installs a previously absent binding association;
other associations remain exact, independently of the prepared value's type. -/
theorem handle_preserves_accepted (runtime : EventGraphRuntime graph)
    (before after : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime before message = some after)
    (field : graph.Field) (candidate : Handle graph) (present : before.accepted field =
      some candidate) : after.accepted field = some candidate := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | opening event named raw =>
      rw [(handle_resolution_tables runtime before after ⟨id, .opening event named raw⟩
        (fun _ _ impossible => by cases impossible) accepted).1]
      exact present
  | commitment event named =>
      have table := (handle_commitment_tables runtime before after id event named accepted).2.1
      obtain ⟨_, _, _, _, _, _, _, _, _, vacant, _⟩ :=
        handle_commitment_conditions runtime before after id event named accepted
      rw [table]
      by_cases same : field = .inr event
      · subst field
        rw [vacant] at present
        cases present
      · rw [Function.update_of_ne same]
        exact present

end Vegas.EventGraphRuntime
