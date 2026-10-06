/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication

/-! # Commitment binding from submission onward

An authored commitment fixes its handle before entering the pending pool.
Every subsequent native action preserves that fixed meaning, including
private preparation, competing submissions, delivery, and inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

theorem privateStep_lookup_of_not_fresh (state : State graph) (who : Player)
    (command : PrivateCommand graph) (candidate : Handle graph)
    (fixed : state.candidates.lookup candidate ≠ .fresh) :
    (privateStep state who command).candidates.lookup candidate =
      state.candidates.lookup candidate := by
  cases command with
  | prepare serial raw =>
      exact state.candidates.lookup_prepare_eq_of_not_fresh
        candidate who (.prepared serial) raw fixed

theorem handle_lookup_of_not_fresh (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (candidate : Handle graph) (fixed : state.candidates.lookup candidate ≠ .fresh)
    (accepted : handle runtime state message = some next) :
    next.candidates.lookup candidate = state.candidates.lookup candidate := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | commitment event selected =>
      rw [(handle_commitment_tables runtime state next id event selected accepted).1]
      exact state.candidates.lookup_freeze_eq_of_not_fresh candidate selected fixed
  | opening event selected raw =>
      rw [(handle_resolution_tables runtime state next _ (by intros; simp) accepted).2]
  | malformed raw => simp [handle] at accepted

end Vegas.EventGraphRuntime
