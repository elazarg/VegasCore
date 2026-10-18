/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastQuietProperReward
import Vegas.Examples.CommitSeedBroadcastProperTimingContext
import Vegas.Examples.CommitSeedBroadcastInitialQuietControl

/-! # The whole proper continuation from the actual quiet fifth-command frame -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The quiet fifth-command execution is genuine under every original seed;
its construction imposes no restriction on later assessed initial prescriptions. -/
theorem quiet_start_fixed_trace (seed : Seeds) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - 5, none, quietStart⟩)) := by
  have covered : ∀ who past view action,
      action ∈ ((fun _ => app.silentPolicy) who past view).support →
        action ∈ countedMenu.actions who past view := by
    intro who past view action supported
    rw [app.silentPolicy_cases past view action supported]
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  exact countedMenu.trace_roundsFrom initial horizon (family seed) (fun _ => app.silentPolicy)
    covered 5 (by decide) quietStart (by
      rw [ReactiveApplication.roundsFrom, initial, PMF.pure_bind]
      change quietStart ∈ (app.runRounds (family seed) (fun _ => app.silentPolicy) 5
        initialExecution).support
      rw [quietStart_law seed (fun _ => app.silentPolicy) (fun _ => rfl),
        PMF.mem_support_pure_iff])

/-- The original private service experiment is unfiltered at the quiet frame.
This is a marginal of the actual initialized joint scheduler law. -/
theorem quiet_start_original_seed_posterior :
    implementation.posterior quietStart.environmentRecall = nativeSeedLaw := by
  let players : Player → app.Policy := fun _ => app.silentPolicy
  have fixed (seed : Seeds) : app.runRounds (family seed) players 5 initialExecution =
      PMF.pure quietStart := quietStart_law seed players (fun _ => rfl)
  have mixed : app.runRounds scheduler players 5 initialExecution = PMF.pure quietStart := by
    have realization := original_realize players 5 initialState
    change (nativeSeedLaw.bind fun seed => app.runRounds (family seed) players 5
      initialExecution) = app.runRounds scheduler players 5 initialExecution at realization
    rw [← realization]
    simp_rw [fixed]
    exact PMF.bind_const _ _
  have joint := app.schedulerMixture_joint nativeSeedLaw family players 5 initialState
  change (nativeSeedLaw.bind fun seed =>
      (app.runRounds (family seed) players 5 initialExecution).map fun next => (next, seed)) =
    (app.runRounds scheduler players 5 initialExecution).bind
      (fun next => (implementation.posterior next.environmentRecall).map
        fun seed => (next, seed)) at joint
  simp_rw [fixed] at joint
  rw [mixed, PMF.pure_bind] at joint
  have marginal := congrArg (fun law : PMF (app.Execution × Seeds) => law.map Prod.snd) joint
  simpa only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.bind_const,
    PMF.bind_pure] using marginal.symm

/-- Every bad foreign owner misses from the actual quiet frame under its
unchanged assessed strategy, independently of later focal responses. -/
theorem quiet_start_bad_foreign_unaccepted
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (other : Player) (bad : seed.2 other = false)
    (selected : players other = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) other)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players (horizon - 5) quietStart).support) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate other) other final := by
  let trace := (quiet_start_fixed_trace seed).some
  obtain ⟨first, word, firstRequest, zero⟩ := frame_five_initial_record seed (horizon - 5)
    quietStart trace quietStart_length other
  exact foreign_singleton_bad_no_helper_unaccepted assessment equilibrium seed supportedSeed
    (horizon - 5) quietStart trace other bad (by rw [quietStart_length])
    (by rw [quietStart_length]; omega) first word firstRequest zero (by rfl)
    players covered selected final reached

/-- The literal quiet initial record is already consistent with proper play. -/
theorem quiet_start_proper_consistent (seed : Seeds) (owner : Player) :
    (scheduledProperPolicy 2 owner).Consistent (quietStart.recall owner) := by
  obtain ⟨first, word, firstRequest, zero⟩ := frame_five_initial_record seed (horizon - 5)
    quietStart (quiet_start_fixed_trace seed).some quietStart_length owner
  have same : first = initialWaitEntry owner :=
    (List.cons.inj (word.symm.trans (quietStart_recall owner))).1
  have silent : first.action.transmission = none := by rw [same]; rfl
  rw [word]
  exact proper_clock_two_initial_wait_consistent owner first firstRequest zero silent

/-- The native seed reward remains a lower bound starting at the quiet frame,
without assuming that assessed opponents would have chosen the preceding WAITs. -/
theorem quiet_start_proper_clock_two_payoff_lower
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
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players (horizon - 5) quietStart).support) :
    (if seed.2 owner then
      if ∃ other : Player, other ≠ owner ∧ seed.2 other = false then (1 : ℝ) else 0
      else -(3 / 2)) ≤ netPayoff (app.finished final) owner := by
  classical
  obtain ⟨trace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 (horizon - 5) quietStart final
      (by simpa only [Nat.zero_add] using (quiet_start_fixed_trace seed).some) reached
  by_cases good : seed.2 owner = true
  · have recovered : players owner =
        (scheduledProperPolicy 2 owner).recover (scheduledProperPolicy 2 owner) := by
      rw [selected]
      funext earlier view
      simp only [ReactiveApplication.Policy.recover, ite_self]
    have invariant := (scheduledProperPolicy 2 owner).recover_invariant
      (scheduledProperPolicy 2 owner) owner players recovered
    have faithful := invariant.runRounds (family seed) (horizon - 5) quietStart final
      (quiet_start_proper_consistent seed owner) reached
    have admitted := proper_clock_two_consistent_good_original_admission seed owner good final
      trace faithful
    have survives := scheduled_proper_original_binding_survives 2 seed ⟨0, none, final⟩ trace
      owner faithful admitted
    rw [ite_eq_left good]
    by_cases missed : ∃ other : Player, other ≠ owner ∧ seed.2 other = false
    · obtain ⟨other, different, bad⟩ := missed
      have missing := quiet_start_bad_foreign_unaccepted assessment equilibrium seed supportedSeed
        players covered other bad (foreign other different) final reached
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
