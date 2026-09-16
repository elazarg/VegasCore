/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReachedActions
import Vegas.Pending.PhaseFrame
import Vegas.Pending.DeviationServiceSafety

/-! # Ownership at replay endpoints -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- A supported run that starts outside the focal owner's cursor and ends at
one of its cursors must have strictly advanced the immutable graph phase. -/
theorem runPolicies_phase_lt_of_owned_endpoint
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (focal : Player) {suffix : Graph Player L Γ Δ}
    {ideal : VEnv L Γ} {values : PublicValues Γ} {bindings : Bindings Player}
    {candidates : CommitmentCandidates Player Slot (Raw L)} {pc clock enteredAt : Nat}
    (current final : runtime.application.PolicyExecution)
    (currentState : current.native.application =
      .running suffix ideal values bindings candidates pc clock enteredAt)
    (notCurrent : ¬ current.native.application.IsOwnedBy (some focal))
    (finalOwned : final.native.application.IsOwnedBy (some focal))
    (supported : final ∈ (runtime.application.runPolicies players environment schedule
      current).support) :
    current.native.application.phase < final.native.application.phase := by
  have monotone := runtime.runPolicies_phase_mono players environment schedule
    current final supported
  rcases monotone.lt_or_eq with advanced | same
  · exact advanced
  · exfalso
    have finalPhase : final.native.application.phase = pc := by
      rw [← same, currentState]
      rfl
    obtain ⟨nextCandidates, nextClock, nextEnteredAt, finalState⟩ :=
      runtime.runPolicies_running_eq_of_phase_eq suffix ideal values bindings candidates
        pc clock enteredAt players environment schedule current final currentState supported
        finalPhase
    apply notCurrent
    rw [currentState]
    rw [finalState] at finalOwned
    cases suffix <;> simp_all [State.IsOwnedBy]

/-- Realizing a graph action owned by `focal` implies that its source state is
at a focal-owned bind or resolve cursor. -/
theorem State.RealizesOwnAction.before_isOwnedBy
    {before after : State Player L Δ} {action : OwnAction Player L}
    (realizes : State.RealizesOwnAction before action after) (focal : Player)
    (owner : (match action with
      | .bind actor _ _ _ => actor
      | .resolve actor _ _ => actor) = focal) :
    before.IsOwnedBy (some focal) := by
  cases realizes <;> simp_all [State.IsOwnedBy]

end Vegas.GraphRuntime
