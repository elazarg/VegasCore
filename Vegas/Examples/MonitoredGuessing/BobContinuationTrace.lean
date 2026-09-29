/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.BobContinuation
import Vegas.Examples.MonitoredGuessing.RestrictedAliceSupport
import Vegas.Examples.MonitoredGuessing.FinalComparison

/-! # Actual native histories for the receiver's continuation

The four service commands after Bob contain no player response. Their supported
executions therefore give actual bounded raw histories independently of the
policy family used to write the interaction law.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory.Math.Probability

theorem bob_service_policy_irrel (left right : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) :
    nativeRuntime.runInteractionPlan nativeLeaks left nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication, .grant alicePublication]
      execution =
    nativeRuntime.runInteractionPlan nativeLeaks right nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication, .grant alicePublication]
      execution := by
  have resume (players : Player → nativeApp.Policy) :
      nativeApp.resume players none = PMF.pure := rfl
  simp only [runInteractionPlan, PMF.bind_pure]
  rw [nativeRuntime.interaction_includeLatest_environment,
    nativeRuntime.interaction_includeLatest_environment]
  simp only [interactionStep, interactionInstruction, PMF.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, resume, PMF.bind_pure]

theorem bob_response_to_alice_trace (players : Player → nativeApp.Policy) (bit : Bool)
    (response : nativeApp.Action)
    (available : response ∈ nativeMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (next : nativeApp.Execution)
    (supported : next ∈ ((nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication, .grant alicePublication]
      ((quietBob bit).respond nativeApp bob response)).bind fun execution =>
        execution.environmentStep nativeApp (.activate alice)).support) :
    Nonempty (nativeArena.Trace (some ⟨4, some alice, next⟩)) := by
  obtain ⟨granted, prior, activated⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  have initialPosition : ((quietBob bit).respond nativeApp bob response).environmentRecall.length =
      (nativePlan.take 5).length := by
    rw [nativeApp.respond_environmentRecall]
    rfl
  have cursor := nativeRuntime.runInteractionPlan_recall nativeLeaks players nativeNetwork _
    ((quietBob bit).respond nativeApp bob response) granted prior
  rw [nativeApp.respond_environmentRecall] at cursor
  change granted.environmentRecall.length = 9 at cursor
  rw [bob_service_policy_irrel players nativeMenu.uniformResponses] at prior
  have rounds := native_segment_rounds nativeMenu.uniformResponses (nativePlan.take 5)
    [.includeLatest bobPublication bob, .tick, .expire bobPublication, .grant alicePublication]
    (nativePlan.drop 9) rfl ((quietBob bit).respond nativeApp bob response) initialPosition
  rw [← rounds] at prior
  obtain ⟨quiet⟩ := quiet_bob_trace bit
  obtain ⟨responded⟩ := nativeMenu.trace_respond nativeInitialLaw nativeHorizon nativeScheduler 9
    (quietBob bit) bob response quiet available
  obtain ⟨before⟩ := nativeMenu.trace_runRounds nativeInitialLaw nativeHorizon nativeScheduler
    nativeMenu.uniformResponses (fun who past view action member =>
      (nativeMenu.uniformResponses_support who past view action).mp member) 5 4
      ((quietBob bit).respond nativeApp bob response) granted responded prior
  exact nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler 4 granted next
    (.activate alice) before (by
      simp only [nativeScheduler, cursor]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) activated

theorem before_alice_trace (bit guess : Bool) :
    Nonempty (nativeArena.Trace (some ⟨4, some alice, beforeAlice bit guess⟩)) := by
  refine bob_response_to_alice_trace (fun _ _ _ => PMF.pure nativeSilent) bit
    (choiceAction bobPublication bobHandle true guess) ?_ (beforeAlice bit guess) ?_
  · cases guess with
    | false => exact native_silent_available _ _ _
    | true => exact native_opening_available bob _ _ bobPublication bobHandle trivial true
  · rw [bob_to_granted_alice, PMF.pure_bind, activate_alice]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem before_alice_false_local (bit : Bool) : FinalResponseLocal (beforeAlice bit false) := by
  obtain ⟨trace⟩ := before_alice_trace bit false
  apply final_history_local ⟨4, some alice, beforeAlice bit false⟩ trace rfl
  intro first member
  change first ∈ ([] : List (Message Player (WitnessedPacket nativeGraph))) at member
  cases member

theorem wrong_address_alice_local (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (available : (⟨some (.submit submission)⟩ : nativeApp.Action) ∈
      nativeMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication)
    (next : nativeApp.Execution) (supported : next ∈ (bobToAlice players bit submission).support) :
    FinalResponseLocal next := by
  obtain ⟨trace⟩ := bob_response_to_alice_trace players bit ⟨some (.submit submission)⟩ available
    next supported
  have input := wrong_address_alice_input players bit submission wrong next supported
  apply final_history_local ⟨4, some alice, next⟩ trace rfl
  have recall : next.recall alice = (beforeAlice bit false).recall alice := congrArg Prod.fst input
  change nativeRuntime.UniqueEventOutput nativeLeaks alice alicePublication (next.recall alice)
  rw [recall]
  intro first member
  change first ∈ ([] : List (Message Player (WitnessedPacket nativeGraph))) at member
  cases member

end Vegas.Examples.MonitoredGuessing.Restricted
