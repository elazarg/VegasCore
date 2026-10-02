/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResolutionIncentives
import Vegas.Examples.MonitoredGuessing.NativeSchedule

/-! # Exact final opening and the terminal native summary -/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem resolution_plan_invariant (players : Player → nativeApp.Policy)
    (predicate : EventGraphRuntime.State nativeGraph → Prop)
        (invariant : nativeApp.Invariant predicate)
    (plan : List (ServiceInstruction nativeGraph)) (before after : nativeApp.Execution)
    (valid : predicate before.application)
    (supported : after ∈
      (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork plan before).support) :
    predicate after.application := by
  induction plan generalizing before with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp supported; exact valid
  | cons instruction rest ih =>
      obtain ⟨middle, reached, moved⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
      obtain ⟨command, _, executed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle ((ReactiveApplication.Invariant.policyInvariant nativeApp invariant
        players).dispatch command before middle
        valid executed) moved

theorem resolution_application_receipts (players : Player → nativeApp.Policy)
    (command : EnvironmentCommand nativeGraph) (before after : nativeApp.Execution)
    (supported : after ∈ (nativeApp.dispatch players (.application command) before).support) :
    after.receipts = before.receipts := by
  change after ∈ ((before.environmentStep nativeApp (.application command)).bind
    PMF.pure).support at supported
  rw [PMF.bind_pure] at supported
  obtain ⟨updated, moved, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ moved
  rfl

theorem resolution_clock_tail_receipts (players : Player → nativeApp.Policy)
    (before after : nativeApp.Execution)
    (supported : after ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.tick, .tick, .expire alicePublication] before).support) :
    after.receipts = before.receipts := by
  obtain ⟨first, firstMem, restMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨second, secondMem, lastMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ restMem)
  simp only [runInteractionPlan, PMF.bind_pure] at lastMem
  have firstEq := resolution_application_receipts players .advanceClock before first
    (by simpa only [interactionStep, interactionInstruction, PMF.pure_bind] using firstMem)
  have secondEq := resolution_application_receipts players .advanceClock first second
    (by simpa only [interactionStep, interactionInstruction, PMF.pure_bind] using secondMem)
  have finalEq := resolution_application_receipts players (.expire alicePublication) second after
    (by simpa only [interactionStep, interactionInstruction, PMF.pure_bind] using lastMem)
  exact finalEq.trans (secondEq.trans firstEq)

def resolutionTail : List (ServiceInstruction nativeGraph) :=
  [.includeLatest alicePublication alice, .tick, .tick, .expire alicePublication]

/-- The actual four-instruction suffix preserves Bob's result and every earlier
charge, while the ordinary successful opening incurs no additional charge. -/
theorem resolution_tail_summary (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess)
    (ready : execution.application.config.cut.Ready alicePublication)
    (timely : execution.application.WithinDeadline nativeRuntime alicePublication)
    (serials : execution.network.SerialsBeforeNext) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      (execution.respond nativeApp alice
        (nativeOpeningAction alicePublication aliceHandle bit))).map
          (fun final => (nativeResults final.application.config, rejectedAlice final.receipts)) =
      PMF.pure (Results.mk (.success bit) guess, rejectedAlice execution.receipts) := by
  obtain ⟨opened, accepted, published⟩ := resolution_opening_accepted bit execution.application
    valid alicePublication ready timely (execution.network.nextSerial alice)
  have accepted' : handle nativeRuntime execution.application
      ⟨(alice, execution.network.nextSerial alice),
        .opening alicePublication aliceHandle ⟨.bool, bit⟩⟩ = some opened := accepted
  have published' : alicePublicationRef.get? opened.config.store = some (.success bit) := published
  have inclusion := resolution_opening_inclusion players execution alice alicePublication
    aliceHandle bit opened serials accepted'
  have bobInvariant := nativeRuntime.reactiveStoreInvariant nativeLeaks
    (.inr bobPublication) guess
  have aliceInvariant := nativeRuntime.reactiveStoreInvariant nativeLeaks
    (.inr alicePublication) (.success bit)
  have bobOpened : bobPublicationRef.get? opened.config.store = some guess :=
    bobInvariant.handle execution.application
      ⟨(alice, execution.network.nextSerial alice),
        ⟨.opening alicePublication aliceHandle ⟨.bool, bit⟩, none, some ⟨alicePublication⟩⟩⟩
      opened stored ((reactiveApplication_handle_of_tokenValid nativeRuntime nativeLeaks _ _
        (WitnessedPacket.tokenValid_opening _ _ _ _)).trans accepted')
  apply pmf_eq_pure_of_support_subset_singleton
  intro summary supported
  change summary = _
  obtain ⟨final, finalMem, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨middle, middleMem, tailMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ finalMem)
  have paired : (middle.application, middle.receipts) =
      (opened, execution.receipts ++ [((alice, execution.network.nextSerial alice), true)]) := by
    apply (PMF.mem_support_pure_iff _ _).mp
    rw [← inclusion, PMF.support_map]
    exact ⟨middle, middleMem, rfl⟩
  have appEq : middle.application = opened := congrArg Prod.fst paired
  have aliceStored := resolution_plan_invariant players _ aliceInvariant
    [.tick, .tick, .expire alicePublication] middle final
      (by rw [appEq]; exact published') tailMem
  have bobStored := resolution_plan_invariant players _ bobInvariant
    [.tick, .tick, .expire alicePublication] middle final
      (by rw [appEq]; exact bobOpened) tailMem
  change alicePublicationRef.get? final.application.config.store = some (.success bit)
    at aliceStored
  change bobPublicationRef.get? final.application.config.store = some guess at bobStored
  have receiptEq := (resolution_clock_tail_receipts players middle final tailMem).trans
    (congrArg Prod.snd paired)
  simp only [nativeResults, aliceStored, bobStored, Option.getD_some, receiptEq,
    rejectedAlice_accepted]

theorem resolution_tail_alice_value (deposit : ℝ) (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess)
    (ready : execution.application.config.cut.Ready alicePublication)
    (timely : execution.application.WithinDeadline nativeRuntime alicePublication)
    (serials : execution.network.SerialsBeforeNext) :
    expect (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      (execution.respond nativeApp alice
        (nativeOpeningAction alicePublication aliceHandle bit)))
          (nativeExecutionUtility deposit alice) =
      correctness (.success bit) guess -
        if rejectedAlice execution.receipts then deposit else 0 := by
  have summary := resolution_tail_summary players execution bit guess valid stored ready
    timely serials
  have expected := congrArg (fun law : PMF (Results × Bool) =>
    expect law (fun outcome => utility outcome.1 alice - if outcome.2 then deposit else 0)) summary
  rw [expect_map, expect_pure] at expected
  change expect _ (fun final => nativeExecutionUtility deposit alice final) = _
  simpa only [nativeExecutionUtility, utility_alice, openingPenalty, sub_zero, true_and,
    Function.comp_def,
    eq_self_iff_true]
    using expected

theorem resolution_finish_alice_value (deposit : ℝ) (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess)
    (ready : execution.application.config.cut.Ready alicePublication)
    (timely : execution.application.WithinDeadline nativeRuntime alicePublication)
    (serials : execution.network.SerialsBeforeNext)
    (position : execution.environmentRecall.length = 8)
    (opens : players alice (execution.recall alice) (execution.observe nativeApp alice) =
      PMF.pure (nativeOpeningAction alicePublication aliceHandle bit)) :
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨4, some alice, execution⟩)) (nativeUtility deposit alice) =
      correctness (.success bit) guess -
        if rejectedAlice execution.receipts then deposit else 0 := by
  have finish := native_finish_response players (nativePlan.take 7) resolutionTail alice
    rfl execution position
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨4, some alice, execution⟩) = _ at finish
  rw [finish, opens, PMF.pure_bind, expect_map]
  exact resolution_tail_alice_value deposit players execution bit guess valid stored ready
    timely serials

/-- All raw policies are compared with the same previously incurred liability. -/
theorem resolution_finish_alice_dominates (deposit : ℝ) (nonnegative : 0 ≤ deposit)
    (prescribed alternative : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (bit : Bool) (guess : PublicationResult Bool)
    (valid : NativeFixed bit execution.application)
    (stored : bobPublicationRef.get? execution.application.config.store = some guess)
    (ready : execution.application.config.cut.Ready alicePublication)
    (timely : execution.application.WithinDeadline nativeRuntime alicePublication)
    (serials : execution.network.SerialsBeforeNext)
    (position : execution.environmentRecall.length = 8)
    (opens : prescribed alice (execution.recall alice) (execution.observe nativeApp alice) =
      PMF.pure (nativeOpeningAction alicePublication aliceHandle bit)) :
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler alternative
      (some ⟨4, some alice, execution⟩)) (nativeUtility deposit alice) ≤
    expect (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler prescribed
      (some ⟨4, some alice, execution⟩)) (nativeUtility deposit alice) := by
  rw [resolution_finish_alice_value deposit prescribed execution bit guess valid stored ready
    timely serials position opens]
  exact resolution_finish_payoff_upper deposit nonnegative alternative _ bit guess valid stored

end Vegas.Examples.MonitoredGuessing
