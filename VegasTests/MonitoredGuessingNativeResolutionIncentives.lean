/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeResolutionService
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveResponseEvaluation

/-! # Final opening incentives retain every earlier liability

An arbitrary continuation cannot change Bob's settled guess, publish a new
Alice value, or erase a rejection receipt. Thus its payoff is bounded by the
ordinary successful opening with the already incurred charge.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem rejectedAlice_mono {before after : List (MessageId Player × Bool)}
    (retained : before <+: after) (rejected : rejectedAlice before = true) :
    rejectedAlice after = true := by
  obtain ⟨suffix, rfl⟩ := retained
  change (before ++ suffix).any _ = true
  rw [List.any_append]
  change (rejectedAlice before || rejectedAlice suffix) = true
  rw [rejected]
  rfl

theorem resolution_charge_mono (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (before after : nativeApp.Execution) (retained : before.receipts <+: after.receipts) :
    (if rejectedAlice before.receipts then deposit else 0) ≤
      (if rejectedAlice after.receipts then deposit else 0) := by
  cases prior : rejectedAlice before.receipts with
  | false =>
      cases later : rejectedAlice after.receipts
      · exact le_rfl
      · exact nonnegative
  | true => rw [rejectedAlice_mono retained prior]

theorem resolution_game_payoff_upper (bit : Bool) (state : State nativeGraph)
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

theorem resolution_execution_payoff_upper (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (bit : Bool) (before after : nativeApp.Execution)
    (valid : NativeFixed bit after.application)
    (guess : PublicationResult Bool)
    (stored : bobPublicationRef.get? after.application.config.store = some guess)
    (receipts : before.receipts <+: after.receipts) :
    nativeExecutionUtility deposit alice after ≤ correctness (.success bit) guess -
      if rejectedAlice before.receipts then deposit else 0 := by
  have bound := resolution_game_payoff_upper bit after.application valid
  have same : (nativeResults after.application.config).bob = guess := by
    simp [nativeResults, stored]
  rw [same] at bound
  have charge := resolution_charge_mono deposit nonnegative before after receipts
  change utility (nativeResults after.application.config) alice -
    (if alice = alice ∧ rejectedAlice after.receipts = true then deposit else 0) ≤ _
  simp only [true_and]
  exact sub_le_sub bound charge

theorem resolution_finish_retains (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit control.execution.application)
    (stored : bobPublicationRef.get? control.execution.application.config.store = some guess)
    (result : nativeApp.ProtocolState)
    (supported : result ∈ (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler
      players (some control)).support) :
    ∃ final, result = some final ∧ NativeFixed bit final.execution.application ∧
      bobPublicationRef.get? final.execution.application.config.store = some guess ∧
      control.execution.receipts <+: final.execution.receipts := by
  let predicate := fun execution : nativeApp.Execution =>
    NativeFixed bit execution.application ∧
      bobPublicationRef.get? execution.application.config.store = some guess ∧
      control.execution.receipts <+: execution.receipts
  have storeInvariant : nativeApp.Invariant (fun state =>
      bobPublicationRef.get? state.config.store = some guess) :=
    nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr bobPublication) guess
  have invariant : nativeApp.PolicyInvariant players predicate := {
    respond := by
      rintro execution who action ⟨fixed, bound, prior⟩ _
      refine ⟨(native_fixed_invariant bit).respond execution who action fixed,
        storeInvariant.respond execution who action bound, ?_⟩
      rw [nativeApp.respond_receipts]
      exact prior
    environment := by
      rintro execution next command ⟨fixed, bound, prior⟩ reached
      exact ⟨(native_fixed_invariant bit).environmentStep execution next command fixed reached,
        storeInvariant.environmentStep execution next command bound reached,
        prior.trans (nativeApp.environmentStep_receipts_prefix execution next command reached)⟩ }
  obtain ⟨final, reached, rfl⟩ := FinDist.support_map .. ▸ supported
  obtain ⟨resumed, resumedMem, finalMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  exact ⟨_, rfl, invariant.runRounds nativeScheduler control.remaining resumed final
    (invariant.resume control.actor control.execution resumed ⟨valid, stored, by rfl⟩ resumedMem)
    finalMem⟩

/-- The upper bound quantifies all continuation policies and all earlier
rejection histories. The charge already incurred is subtracted from both the
prescribed benchmark and every deviation; it supplies no fresh deterrence. -/
theorem resolution_finish_payoff_upper (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (players : Player → nativeApp.Policy) (control : nativeApp.Control)
    (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit control.execution.application)
    (stored : bobPublicationRef.get? control.execution.application.config.store = some guess) :
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players (some control)).expect
      (nativeUtility deposit alice) ≤ correctness (.success bit) guess -
        if rejectedAlice control.execution.receipts then deposit else 0 := by
  apply FinDist.expect_le_of_forall
  intro result supported
  obtain ⟨final, rfl, fixed, bound, receipts⟩ :=
    resolution_finish_retains players control bit guess valid stored result supported
  exact resolution_execution_payoff_upper deposit nonnegative bit control.execution
    final.execution fixed guess bound receipts

end VegasTests.MonitoredGuessing
