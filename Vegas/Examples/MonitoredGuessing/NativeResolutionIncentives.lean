/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResolutionService
import Vegas.Examples.MonitoredGuessing.NativeLiability
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveResponseEvaluation

/-! # Final opening incentives retain every earlier liability

An arbitrary continuation cannot change Bob's settled guess, publish a new
Alice value, or erase a rejection receipt. Thus its payoff is bounded by the
ordinary successful opening with the already incurred charge.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem resolution_charge_mono (charge : ℝ) (nonnegative : 0 ≤ charge)
    (before after : nativeApp.Execution) (retained : aliceLiability before = true →
      aliceLiability after = true) :
    (if aliceLiability before then charge else 0) ≤
      (if aliceLiability after then charge else 0) := by
  cases prior : aliceLiability before with
  | false =>
      cases later : aliceLiability after
      · exact le_rfl
      · exact nonnegative
  | true => rw [retained prior]

theorem resolution_game_payoff_upper (bit : Bool) (state : EventGraphRuntime.State nativeGraph)
    (valid : NativeFixed bit state) :
    utility (nativeResults state.config) alice ≤
      correctness (.success bit) (nativeResults state.config).bob := by
  rw [utility_alice]
  rcases valid.alice_results with failed | opened
  · rw [failed]
    change (0 : ℝ) - 4 ≤ _
    cases bit <;> cases (nativeResults state.config).bob <;>
      norm_num [correctness, PublicationResult.isSuccess]
  · rw [opened]
    exact sub_le_self _ (by rfl)

theorem resolution_execution_payoff_upper (charge : ℝ) (nonnegative : 0 ≤ charge)
    (bit : Bool) (before after : nativeApp.Execution)
    (valid : NativeFixed bit after.application)
    (guess : PublicationResult Bool)
    (stored : bobPublicationRef.get? after.application.config.store = some guess)
    (liability : aliceLiability before = true → aliceLiability after = true) :
    nativeComparisonExecutionUtility charge alice after ≤ correctness (.success bit) guess -
      if aliceLiability before then charge else 0 := by
  have bound := resolution_game_payoff_upper bit after.application valid
  have same : (nativeResults after.application.config).bob = guess := by
    simp [nativeResults, stored]
  rw [same] at bound
  have penalty := resolution_charge_mono charge nonnegative before after liability
  change utility (nativeResults after.application.config) alice -
    (if alice = alice ∧ aliceLiability after = true then charge else 0) ≤ _
  simp only [true_and]
  exact sub_le_sub bound penalty

theorem resolution_finish_retains (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit control.execution.application)
    (stored : bobPublicationRef.get? control.execution.application.config.store = some guess)
    (result : nativeApp.ProtocolState)
    (supported : result ∈ (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      players (some control)).support) :
    ∃ final, result = some final ∧ NativeFixed bit final.execution.application ∧
      bobPublicationRef.get? final.execution.application.config.store = some guess ∧
      (aliceLiability control.execution = true → aliceLiability final.execution = true) := by
  let predicate := fun execution : nativeApp.Execution =>
    NativeFixed bit execution.application ∧
      bobPublicationRef.get? execution.application.config.store = some guess ∧
      (aliceLiability control.execution = true → aliceLiability execution = true)
  have storeInvariant : nativeApp.Invariant (fun state =>
      bobPublicationRef.get? state.config.store = some guess) :=
    nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr bobPublication) guess
  have invariant : nativeApp.PolicyInvariant players predicate := {
    respond := by
      rintro execution who action ⟨fixed, bound, prior⟩ supported
      refine ⟨(native_fixed_invariant bit).respond execution who action fixed,
        storeInvariant.respond execution who action bound, ?_⟩
      intro liable
      exact (aliceLiability_policyInvariant players).respond execution who action (prior liable)
        supported
    environment := by
      rintro execution next command ⟨fixed, bound, prior⟩ reached
      exact ⟨(native_fixed_invariant bit).environmentStep execution next command fixed reached,
        storeInvariant.environmentStep execution next command bound reached,
        fun liable => (aliceLiability_policyInvariant players).environment execution next
          command (prior liable) reached⟩ }
  obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨resumed, resumedMem, finalMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  exact ⟨_, rfl, invariant.runRounds nativeScheduler control.remaining resumed final
    (invariant.resume control.actor control.execution resumed ⟨valid, stored, id⟩ resumedMem)
    finalMem⟩

/-- The upper bound quantifies all continuation policies and all earlier
rejection histories. The charge already incurred is subtracted from both the
prescribed benchmark and every deviation; it supplies no fresh deterrence. -/
theorem resolution_finish_payoff_upper (charge : ℝ) (nonnegative : 0 ≤ charge)
    (players : Player → nativeApp.Policy) (control : nativeApp.Control)
    (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit control.execution.application)
    (stored : bobPublicationRef.get? control.execution.application.config.store = some guess) :
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players (some control))
      (nativeComparisonUtility charge alice) ≤ correctness (.success bit) guess -
        if aliceLiability control.execution then charge else 0 := by
  refine expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 5 + |charge|)
    (nativeComparisonUtility_abs_le charge alice)) _ ?_
  intro result supported
  obtain ⟨final, rfl, fixed, bound, receipts⟩ :=
    resolution_finish_retains players control bit guess valid stored result supported
  exact resolution_execution_payoff_upper charge nonnegative bit control.execution
    final.execution fixed guess bound receipts

end Vegas.Examples.MonitoredGuessing
