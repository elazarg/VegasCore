/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicies

/-! # Message-application policy history counts

Principal-local policy memory counts exactly that principal's invocations,
including waits, independently of all policies and native transition outcomes.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} (app : MessageApplication Principal)

/-- A principal's policy history grows once for each of that principal's
invocations and is unchanged by every other invocation. -/
theorem runPolicies_principalHistory_length [DecidableEq Principal]
    (who : Principal) (players : Principal → app.PlayerPolicy)
    (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule execution).support) :
    (next.principalHistory who).length =
      (execution.principalHistory who).length +
        schedule.countP (fun invocation =>
          match invocation with
          | .player actor => decide (actor = who)
          | .environment => false) := by
  induction schedule generalizing execution with
  | nil =>
      simp only [runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      simp
  | cons invocation rest ih =>
      simp only [runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have htail := ih middle hnext
      cases invocation with
      | player actor =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          by_cases hactor : actor = who
          · subst actor
            have hhistory := app.playerStep_history_self who execution command middle hstep
            simp only [List.countP_cons, decide_true, if_true]
            rw [htail, hhistory, List.length_append, List.length_singleton]
            omega
          · have hhistory := app.playerStep_other_history actor who
                (Ne.symm hactor) execution command middle hstep
            simp only [List.countP_cons, decide_eq_false hactor,
              Bool.false_eq_true, ↓reduceIte]
            rw [htail, hhistory]
            omega
      | environment =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
          obtain ⟨command, _, hstep⟩ := hmiddle
          have hhistory := congrFun
            (app.environmentStep_principalHistory execution command middle hstep) who
          simp only [List.countP_cons, Bool.false_eq_true, ↓reduceIte]
          rw [htail, hhistory]
          omega

end Interaction.MessageApplication
