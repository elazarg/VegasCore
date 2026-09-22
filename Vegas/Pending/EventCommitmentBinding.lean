/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication
import Interaction.MessageApplicationPolicyLaws

/-! # Commitment binding from submission onward

An authored commitment fixes its handle before entering the pending pool.
Every subsequent native action preserves that fixed meaning, including
private preparation, competing submissions, delivery, replay, and inclusion.
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
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · cases cached : state.remembered event <;> simp [privateStep, owned, cached]
      · simp [privateStep, owned]

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
  | withhold event =>
      rw [(handle_resolution_tables runtime state next _ (by intros; simp) accepted).2]
  | malformed raw => simp [handle] at accepted

/-- Once fixed, a handle's meaning is invariant under an arbitrary finite
native continuation. No honesty, deadline, or inclusion premise is needed. -/
theorem run_candidate_fixed (runtime : EventGraphRuntime graph)
    (before after : runtime.application.State) (actions : List runtime.application.Action)
    (candidate : Handle graph) (fixed : before.application.candidates.lookup candidate ≠ .fresh)
    (supported : after ∈ (runtime.application.run actions before).support) :
    after.application.candidates.lookup candidate =
      before.application.candidates.lookup candidate := by
  apply runtime.application.run_application_invariant
    (fun state => state.candidates.lookup candidate =
      before.application.candidates.lookup candidate)
    _ _ _ _ before after actions rfl supported
  · intro state who command same
    exact (privateStep_lookup_of_not_fresh state who command candidate
      (by rwa [same])).trans same
  · intro state who packet same
    exact (submitStep_lookup_of_not_fresh state who packet candidate
      (by rwa [same])).trans same
  · intro state message next same accepted
    exact (handle_lookup_of_not_fresh runtime state next message candidate
      (by rwa [same]) accepted).trans same
  · intro state command next same member
    rw [(environmentStep_tables runtime state next command member).2]
    exact same

/-- An authored commitment is already binding throughout its pending lifetime
and every later native continuation. An unprepared submission remains unopenable. -/
theorem submitted_commitment_binding (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution) (who : Player)
    (event : graph.EventId) (slot : CandidateSlot graph)
    (actions : List runtime.application.Action) (after : runtime.application.State)
    (supported : after ∈ (runtime.application.run actions
      (runtime.application.afterSubmit execution who
        (.commitment event (who, slot))).native).support) :
    after.application.candidates.lookup (who, slot) =
      (execution.native.application.candidates.freeze (who, slot)).lookup (who, slot) := by
  have fixed := submitStep_commitment_fixed execution.native.application who event slot
  have retained := run_candidate_fixed runtime _ after actions (who, slot) fixed supported
  simpa [MessageApplication.afterSubmit, application, submitStep] using retained

end Vegas.EventGraphRuntime
