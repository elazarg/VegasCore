/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationPolicyTrace
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Exact probabilities of stopped native traces

The recorded snapshots identify every intermediate invocation result. Their
point masses therefore factor into the actual invocation-kernel probabilities.
Stopping is the existing trace projection; the runtime continues unchanged.
The formulas also cover zero-probability traces and dependent random choices.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- A player invocation contributes exactly its policy's command probability.
The native player step is deterministic, and the retained history distinguishes
commands even when their application effects are identical or rejected. -/
theorem invoke_player_prob_of_step
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (initial next : app.PolicyExecution) (command : app.PlayerCommand)
    (hnext : next ∈ (app.playerStep who initial command).support) :
    (app.invoke players environment initial (.player who)).prob next =
      (players who (initial.principalHistory who)
        (State.observe app initial.native who)).prob command := by
  have hpure : ∃ result, app.playerStep who initial command = FinDist.pure result := by
    cases command <;>
      simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
        FinDist.pure_bind] <;> exact ⟨_, rfl⟩
  obtain ⟨result, hresult⟩ := hpure
  have heq : next = result := FinDist.mem_support_pure.mp (hresult ▸ hnext)
  have hsingle : app.playerStep who initial command = FinDist.pure next := heq ▸ hresult
  rw [invoke, FinDist.prob_bind_of_unique_branch _ _ next command]
  · rw [hsingle, FinDist.prob_pure_self, mul_one]
  · intro other _ hother
    have hhistory := (app.playerStep_history_self who initial other next hother).symm.trans
      (app.playerStep_history_self who initial command next hnext)
    exact congrArg MessageInterface.PlayerEntry.command
      (List.cons.inj (List.append_cancel_left hhistory)).1

theorem tracePolicies_prefixThrough_first
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool)
    (schedule : List (@Invocation Principal)) (initial : app.PolicyExecution)
    (trace : app.PolicyTrace)
    (htrace : trace ∈ ((app.tracePolicies players environment schedule initial).map
      (PolicyTrace.prefixThrough release)).support) :
    trace.first = initial := by
  rw [FinDist.support_map] at htrace
  obtain ⟨full, hfull, rfl⟩ := htrace
  exact (full.prefixThrough_first release).trans
    (app.tracePolicies_first players environment schedule initial full hfull)

/-- Actual invocation masses along a queried stopped trace. Shape and initial
snapshot checks contribute zero for inconsistent queries. No independent
sampling or replacement policy is used in this definition. -/
def stoppedPointFactors
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool) :
    List (@Invocation Principal) → app.PolicyExecution → app.PolicyTrace → List ℝ
  | [], initial, trace => [(FinDist.pure (.finish initial)).prob trace]
  | invocation :: rest, initial, trace =>
      if release initial then [(FinDist.pure (.finish initial)).prob trace]
      else match trace with
      | .finish _ => [0]
      | .step recorded tail =>
          (FinDist.pure initial).prob recorded ::
          (app.invoke players environment initial invocation).prob tail.first ::
          stoppedPointFactors players environment release rest tail.first tail

/-- The law is that of the original native runner with its existing prefix
readout. Every invocation contributes its conditional probability; the suffix
after the selected snapshot integrates to one. -/
theorem tracePolicies_prefixThrough_prob_eq_prod
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (release : app.PolicyExecution → Bool)
    (schedule : List (@Invocation Principal)) (initial : app.PolicyExecution)
    (trace : app.PolicyTrace) :
    ((app.tracePolicies players environment schedule initial).map
      (PolicyTrace.prefixThrough release)).prob trace =
        (app.stoppedPointFactors players environment release schedule initial trace).prod := by
  classical
  induction schedule generalizing initial trace with
  | nil => simp only [tracePolicies, FinDist.map_pure, PolicyTrace.prefixThrough,
      stoppedPointFactors, List.prod_singleton]
  | cons invocation rest ih =>
      rw [app.tracePolicies_prefixThrough_cons]
      by_cases hrelease : release initial = true
      · simp only [hrelease, ↓reduceIte, stoppedPointFactors, List.prod_singleton]
      · rw [if_neg hrelease]
        cases trace with
        | finish final =>
            rw [stoppedPointFactors, if_neg hrelease, List.prod_singleton]
            apply FinDist.prob_eq_zero_iff.mpr
            intro hmem
            simp only [FinDist.support_bind, Set.mem_iUnion,
              FinDist.support_map, Set.mem_image] at hmem
            obtain ⟨next, _, tail, _, heq⟩ := hmem
            cases heq
        | step recorded tail =>
            rw [stoppedPointFactors, if_neg hrelease, List.prod_cons, List.prod_cons]
            by_cases heq : recorded = initial
            · subst recorded
              rw [FinDist.prob_pure_self, one_mul, ← FinDist.map_bind,
                FinDist.prob_map_of_injective _ (fun _ _ h => (PolicyTrace.step.inj h).2)]
              rw [FinDist.prob_bind_of_unique_branch _ _ tail tail.first]
              · rw [ih]
              · intro next _ htail
                exact (app.tracePolicies_prefixThrough_first players environment release
                  rest next tail htail).symm
            · rw [FinDist.prob_eq_zero_iff.mpr
                (fun h => heq (FinDist.mem_support_pure.mp h)), zero_mul]
              apply FinDist.prob_eq_zero_iff.mpr
              intro hmem
              simp only [FinDist.support_bind, Set.mem_iUnion,
                FinDist.support_map, Set.mem_image] at hmem
              obtain ⟨next, _, suffix, _, hstep⟩ := hmem
              exact heq (PolicyTrace.step.inj hstep).1.symm

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.invoke_player_prob_of_step'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.invoke_player_prob_of_step

/-- info: 'Interaction.MessageApplication.tracePolicies_prefixThrough_prob_eq_prod'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.tracePolicies_prefixThrough_prob_eq_prod
