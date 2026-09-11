/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Invariants under idle environment service -/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal}

/-- An application-state invariant stable under private preparation is
preserved through arbitrary player traffic when every environment invocation
in the schedule's exact history range is serviced by `wait`. -/
theorem runPolicies_idleEnvironment_invariant
    (app : MessageApplication Principal) [DecidableEq Principal]
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (initial next : app.PolicyExecution)
    (Invariant : app.Application → Prop)
    (hprivate : ∀ state actor command, Invariant state →
      Invariant (app.privateStep state actor command))
    (hidle : ∀ execution : app.PolicyExecution,
      Invariant execution.native.application →
      initial.environmentHistory.length ≤ execution.environmentHistory.length →
      execution.environmentHistory.length < initial.environmentHistory.length +
        schedule.countP Invocation.isEnvironment →
      environment execution.environmentHistory
          (State.environmentView app execution.native) = FinDist.pure .wait)
    (hinvariant : Invariant initial.native.application)
    (hnext : next ∈ (app.runPolicies players environment schedule initial).support) :
    Invariant next.native.application := by
  induction schedule generalizing initial with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hinvariant
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hmiddleInvariant : Invariant middle.native.application := by
        cases invocation with
        | player actor =>
            simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hstep⟩ := hmiddle
            cases command with
            | privateCommand command =>
                simp only [playerStep, PlayerCommand.toAction, advance,
                  MessageApplication.step, FinDist.pure_bind,
                  FinDist.mem_support_pure] at hstep
                subst middle
                exact hprivate _ actor command hinvariant
            | submit payload | replay id | wait =>
                simp only [playerStep, PlayerCommand.toAction, advance,
                  MessageApplication.step, FinDist.pure_bind,
                  FinDist.mem_support_pure] at hstep
                subst middle
                exact hinvariant
        | environment =>
            have hpolicy := hidle initial hinvariant (Nat.le_refl _) (by
              simp [Invocation.isEnvironment])
            simp only [invoke, hpolicy, FinDist.pure_bind, environmentStep_wait,
              FinDist.mem_support_pure] at hmiddle
            subst middle
            exact hinvariant
      have hlength := app.runPolicies_environmentHistory_length players environment
        [invocation] initial middle (by simpa [runPolicies] using hmiddle)
      apply ih middle ?_ hmiddleInvariant hnext
      intro execution hexecution hlo hhi
      apply hidle execution hexecution <;>
        cases invocation <;>
        simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
          Bool.false_eq_true, ↓reduceIte] at hlength ⊢ <;> omega

end Interaction.MessageApplication
