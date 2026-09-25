/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeGuess
import VegasTests.MonitoredGuessingNativeResolutionFinal
import VegasTests.MonitoredGuessingNativeHonest

/-! # Every raw quiet receiver continuation is bounded by a bit-independent guess -/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem quiet_raw_guess_completed (bit : Bool) (response : nativeApp.Action)
    (players : Player → nativeApp.Policy) (next : nativeApp.Execution)
    (supported : next ∈ (quietGuessLaw bit response players).support) :
    bobPublication ∈ next.application.config.cut.completed := by
  let start := (quietBob bit).respond nativeApp bob response
  have fixed : NativeFixed bit start.application :=
    (native_fixed_invariant bit).respond (quietBob bit) bob response (quiet_bob_fixed bit)
  have ready : start.application.config.cut.Ready bobPublication := by
    rw [(nativeRuntime.reactive_respond_application nativeLeaks (quietBob bit) bob response).1]
    exact initial_bob_ready bit
  obtain ⟨entered, activated⟩ := fixed.1.activatedAt_eq_some_of_ready_actor
    bobPublication ready (by rfl)
  have enteredLe := fixed.1.activated_le bobPublication entered activated
  obtain ⟨prior, priorMem, expired, expiredMem, finalMem⟩ :=
    nativeRuntime.runInteractionPlan_support_instruction nativeLeaks players nativeNetwork
      [.includeLatest bobPublication bob, .tick] [] (.expire bobPublication)
      start next supported
  have progress := nativeRuntime.runInteractionPlan_facts nativeLeaks (nativeInputs bit) players
    nativeNetwork _ start prior fixed.1 priorMem
  have expiry := nativeRuntime.interactionStep_facts nativeLeaks (nativeInputs bit) players
    nativeNetwork (.expire bobPublication) prior expired progress.invariant expiredMem
  cases FinDist.mem_support_pure.mp finalMem
  rcases progress.ready_or_completed bobPublication ready with completed | stillReady
  · exact expiry.completed completed
  · apply nativeRuntime.interactionStep_expire_complete nativeLeaks players nativeNetwork
      bobPublication prior next stillReady (by rfl) entered
      (progress.activated bobPublication entered activated stillReady.1) _ expiredMem
    rw [progress.clock]
    change 1 ≤ start.application.clock + 1 - entered
    omega

theorem quiet_raw_guess_stored (bit : Bool) (response : nativeApp.Action)
    (players : Player → nativeApp.Policy) (next : nativeApp.Execution)
    (supported : next ∈ (quietGuessLaw bit response players).support) :
    bobPublicationRef.get? next.application.config.store = some (quietGuess response players) := by
  have completed := quiet_raw_guess_completed bit response players next supported
  have present : (bobPublicationRef.get? next.application.config.store).isSome = true :=
    (next.application.config.output_available bobPublication).mpr completed
  obtain ⟨guess, stored⟩ := Option.isSome_iff_exists.mp present
  have classified := quiet_raw_guess_fixed bit response players next supported
  change (bobPublicationRef.get? next.application.config.store).getD .failure = _ at classified
  rw [stored, Option.getD_some] at classified
  rwa [← classified]

theorem resolution_plan_bob_upper (deposit : ℝ) (players : Player → nativeApp.Policy)
    (plan : List (ServiceInstruction nativeGraph)) (execution : nativeApp.Execution)
    (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan execution).expect
      (nativeExecutionUtility deposit bob) ≤ correctness (.success bit) guess := by
  apply FinDist.expect_le_of_forall
  intro final supported
  have fixed := resolution_plan_invariant players _ (native_fixed_invariant bit) plan
    execution final valid supported
  have bound := resolution_plan_invariant players _
    (nativeRuntime.reactiveStoreInvariant nativeLeaks (.inr bobPublication) guess) plan
    execution final stored supported
  change bobPublicationRef.get? final.application.config.store = some guess at bound
  have bobResult : (nativeResults final.application.config).bob = guess := by
    simp only [nativeResults, bound, Option.getD_some]
  change utility (nativeResults final.application.config) bob -
      (if bob = alice ∧ rejectedAlice final.receipts then deposit else 0) ≤ _
  rw [ite_eq_right (fun condition => (show bob ≠ alice by decide) condition.1), sub_zero,
    utility_bob, bobResult]
  rcases fixed.alice_results with failed | opened
  · rw [failed]
    cases bit <;> cases guess <;> norm_num [correctness, PublicationResult.isSuccess]
  · rw [opened]

theorem quiet_response_bob_value_le (deposit : ℝ) (players : Player → nativeApp.Policy)
    (bit : Bool) (response : nativeApp.Action) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativePlan.drop 5)
      ((quietBob bit).respond nativeApp bob response)).expect
        (nativeExecutionUtility deposit bob) ≤
      correctness (.success bit) (quietGuess response players) := by
  change (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
    (quietGuessPlan ++ [.grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob response)).expect _ ≤ _
  rw [List.append_assoc, runInteractionPlan_append, FinDist.expect_bind]
  apply FinDist.expect_le_of_forall
  intro next supported
  have fixed := resolution_plan_invariant players _ (native_fixed_invariant bit) quietGuessPlan
    ((quietBob bit).respond nativeApp bob response) next
    ((native_fixed_invariant bit).respond (quietBob bit) bob response (quiet_bob_fixed bit))
    supported
  exact resolution_plan_bob_upper deposit players _ next bit (quietGuess response players) fixed
    (quiet_raw_guess_stored bit response players next supported)

end VegasTests.MonitoredGuessing
