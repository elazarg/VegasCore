/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperInitializedAdmission
import Vegas.Examples.CommitSeedBroadcastInitialHelperAdmission
import Vegas.Examples.CommitSeedBroadcastPreparationValue
import Vegas.Examples.CommitSeedBroadcastSeedReward

/-! # The positive initialized reward from quiet proper clock-two play -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- With a quiet initial prefix, every bad foreign seed misses its original
binding under the actual assessed continuation. Hidden preparations remain arbitrary. -/
theorem quiet_initialized_bad_foreign_unaccepted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (waited : ∀ who, players who ((initialCallback who).recall who)
      ((initialCallback who).observe app who) = PMF.pure ⟨none⟩)
    (other : Player) (bad : seed.2 other = false)
    (selected : players other = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) other)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players horizon initialExecution).support) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate other) other final := by
  have split : horizon = 5 + (horizon - 5) := by decide
  rw [split, app.runRounds_add, quietStart_law seed players waited, PMF.pure_bind] at reached
  obtain ⟨trace⟩ := countedMenu.trace_roundsFrom initial horizon (family seed) players covered
    5 (by decide) quietStart (by
      rw [ReactiveApplication.roundsFrom, initial, PMF.pure_bind]
      change quietStart ∈ (app.runRounds (family seed) players 5 initialExecution).support
      rw [quietStart_law seed players waited, PMF.mem_support_pure_iff])
  obtain ⟨first, word, firstRequest, zero⟩ :=
    frame_five_initial_record seed (horizon - 5) quietStart trace quietStart_length other
  exact foreign_singleton_bad_no_helper_unaccepted assessment equilibrium seed supportedSeed
    (horizon - 5) quietStart trace other bad (by rw [quietStart_length])
    (by rw [quietStart_length]; omega) first word firstRequest zero (by rfl)
    players covered selected final reached

/-- The seed reward is a pointwise lower bound on the actual terminal payoff
of the whole initialized proper policy against quiet assessed opponents. -/
theorem quiet_initialized_proper_clock_two_payoff_lower
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (owner : Player) (players : Player → app.Policy)
    (selected : players owner = scheduledProperPolicy 2 owner)
    (foreign : ∀ other, other ≠ owner → players other =
      countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment)
        other)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (waited : ∀ who, players who ((initialCallback who).recall who)
      ((initialCallback who).observe app who) = PMF.pure ⟨none⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players horizon initialExecution).support) :
    (if seed.2 owner then
      if ∃ other : Player, other ≠ owner ∧ seed.2 other = false then (1 : ℝ) else 0
      else -(3 / 2)) ≤ netPayoff (app.finished final) owner := by
  classical
  obtain ⟨trace⟩ := countedMenu.trace_roundsFrom initial horizon (family seed) players covered
    horizon le_rfl final (by
      simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
        using reached)
  simp only [Nat.sub_self] at trace
  by_cases good : seed.2 owner = true
  · have admitted := initialized_proper_clock_two_good_original_admission seed owner good
      players selected covered final reached
    have consistency := (app.consistentRecall_policyInvariant players).runRounds (family seed)
      horizon initialExecution final (fun _ => .nil) reached
    have faithful : (scheduledProperPolicy 2 owner).Consistent (final.recall owner) := by
      simpa only [selected] using consistency owner
    have survives := scheduled_proper_original_binding_survives 2 seed ⟨0, none, final⟩ trace
      owner faithful admitted
    rw [ite_eq_left good]
    by_cases missed : ∃ other : Player, other ≠ owner ∧ seed.2 other = false
    · obtain ⟨other, different, bad⟩ := missed
      have missing := quiet_initialized_bad_foreign_unaccepted assessment equilibrium seed
        supportedSeed players covered waited other bad (foreign other different) final reached
      have failed := counted_fixed_missing_original_publication_failed seed supportedSeed final
        trace other missing
      rw [ite_eq_left ⟨other, different, bad⟩, counted_fixed_endpoint_payoff seed final trace owner,
        ite_eq_right survives, ite_eq_left ⟨other, different, failed⟩]
    · rw [ite_eq_right missed, counted_fixed_endpoint_payoff seed final trace owner,
        ite_eq_right survives]
      split <;> norm_num
  · rw [ite_eq_right good, counted_fixed_endpoint_payoff seed final trace owner]
    split_ifs <;> norm_num

end Vegas.Examples.CommitSeedBroadcast
