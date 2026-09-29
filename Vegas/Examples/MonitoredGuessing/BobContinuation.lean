/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedExecution
import Vegas.Pending.ReactiveSelectionObservation

/-! # Unselected Bob traffic and Alice's next decision input

This fixture gives Alice an empty passive sample. A Bob packet which is not
addressed to Bob's publication remains pending but cannot change her next
decision input. This is a property of the actual observation rule and fixed
service; it does not generalize to a later reader of those pending packets.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def bobSubmission (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    nativeApp.Execution :=
  (quietBob bit).respond nativeApp bob ⟨some (.submit submission)⟩

theorem quiet_bob_response_cases (bit : Bool) (response : nativeApp.Action)
    (available : response ∈ nativeMenu.actions bob [] ((quietBob bit).observe nativeApp bob)) :
    response = nativeSilent ∨
      ∃ submission, response = ⟨some (.submit submission)⟩ := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl rfl
  | some transmission =>
      cases transmission with
      | submit submission => exact Or.inr ⟨submission, rfl⟩
      | replay id =>
          change (⟨some (.replay id)⟩ : nativeApp.Action) ∈
            (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions bob [] _ at available
          rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
            at available
          obtain ⟨message, member, _⟩ := available
          change message ∈ (quietBob bit).network.leaked bob ++
            (quietBob bit).network.ledger at member
          rw [quiet_bob_network] at member
          cases member

theorem wrong_address_selection (bit : Bool) (submission : WitnessedSubmission nativeGraph)
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication) :
    nativeRuntime.reactiveLatest nativeLeaks bobPublication bob
      ((bobSubmission bit submission).observeEnvironment nativeApp) = .wait := by
  have pending : (bobSubmission bit submission).network.pending =
      [⟨(bob, 0), submission.emit (bobSubmission bit submission).application bob
        ((quietBob bit).network.known bob)⟩] := by
    change (quietBob bit).network.pending ++ [_] = _
    rw [quiet_bob_network]
    rfl
  simp only [reactiveLatest, ReactiveApplication.Execution.observeEnvironment,
    MessageNetwork.publicView, pending, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.find?_cons, Message.sender, WitnessedSubmission.emit_call, wrong, false_and,
    and_false, decide_false, List.find?_nil]

theorem wrong_address_inclusion (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob) (bobSubmission bit submission) =
        PMF.pure (waitExecution (bobSubmission bit submission)) := by
  rw [nativeRuntime.interaction_includeLatest_environment, wrong_address_selection bit _ wrong]
  change (PMF.pure _).map _ = _
  rw [PMF.pure_map]
  rfl

private def SameAlice (left right : nativeApp.Execution) : Prop :=
  left.application.playerView alice = right.application.playerView alice ∧
    left.recall alice = right.recall alice ∧
      left.observe nativeApp alice = right.observe nativeApp alice

private theorem same_alice_submission (bit : Bool) (submission : WitnessedSubmission nativeGraph) :
    SameAlice (bobSubmission bit submission) (silentBobResponse bit) := by
  have framed := (submitStep_playerView_other
    (submission.call.register (quietBob bit).application bob) bob alice (by decide)
      submission.call.packet).trans
        (submission.call.register_other (quietBob bit).application bob alice (by decide))
  have observed := nativeRuntime.reactive_response_other_input nativeLeaks (quietBob bit)
    bob alice (by decide) (⟨some (.submit submission)⟩ : nativeApp.Action)
  exact ⟨framed, congrArg Prod.fst observed, congrArg Prod.snd observed⟩

private theorem same_alice_maintenance (left right nextLeft nextRight : nativeApp.Execution)
    (command : EnvironmentCommand nativeGraph)
    (maintenance : ∀ event, command ≠ .executeSample event) (same : SameAlice left right)
    (leftMem : nextLeft ∈ (left.environmentStep nativeApp (.application command)).support)
    (rightMem : nextRight ∈ (right.environmentStep nativeApp (.application command)).support) :
    SameAlice nextLeft nextRight := by
  obtain ⟨leftUpdated, leftMoved, rfl⟩ := PMF.support_map .. ▸ leftMem
  obtain ⟨leftState, leftSupported, rfl⟩ := PMF.support_map .. ▸ leftMoved
  obtain ⟨rightUpdated, rightMoved, rfl⟩ := PMF.support_map .. ▸ rightMem
  obtain ⟨rightState, rightSupported, rfl⟩ := PMF.support_map .. ▸ rightMoved
  have pureStep (state : EventGraphRuntime.State nativeGraph) :
      ∃ result, environmentStep nativeRuntime state command = PMF.pure result := by
    cases command with
    | executeSample event => exact (maintenance event rfl).elim
    | grant event | advanceClock | expire event => exact ⟨_, rfl⟩
  obtain ⟨leftResult, leftPure⟩ := pureStep left.application
  obtain ⟨rightResult, rightPure⟩ := pureStep right.application
  change leftState ∈ (environmentStep nativeRuntime left.application command).support
    at leftSupported
  change rightState ∈ (environmentStep nativeRuntime right.application command).support
    at rightSupported
  rw [leftPure, PMF.mem_support_pure_iff _ _] at leftSupported
  rw [rightPure, PMF.mem_support_pure_iff _ _] at rightSupported
  subst leftState rightState
  have views := nativeRuntime.maintenance_playerView_congr left.application right.application
    alice command maintenance same.1
  rw [leftPure, rightPure, PMF.pure_map, PMF.pure_map] at views
  have applicationEq : leftResult.playerView alice = rightResult.playerView alice :=
    (PMF.mem_support_pure_iff _ _).mp (views ▸ (PMF.mem_support_pure_iff _ _).mpr rfl)
  refine ⟨applicationEq, same.2.1, ?_⟩
  have observed := congrArg (fun view : PlayerView nativeGraph =>
    (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
      ReactivePlayerView nativeGraph)) applicationEq
  change nativeApp.observePlayer leftResult alice = nativeApp.observePlayer rightResult alice
    at observed
  change (⟨left.network.observe alice, nativeApp.observePlayer leftResult alice,
    left.receipts⟩ : nativeApp.PlayerView) =
      ⟨right.network.observe alice, nativeApp.observePlayer rightResult alice, right.receipts⟩
  rw [observed]
  congr 1
  · exact congrArg ReactiveApplication.PlayerView.messages same.2.2
  · exact congrArg ReactiveApplication.PlayerView.receipts same.2.2

private theorem same_alice_activation (left right nextLeft nextRight : nativeApp.Execution)
    (same : SameAlice left right)
    (leftMem : nextLeft ∈ (left.environmentStep nativeApp (.activate alice)).support)
    (rightMem : nextRight ∈ (right.environmentStep nativeApp (.activate alice)).support) :
    SameAlice nextLeft nextRight := by
  have activation (execution : nativeApp.Execution) :
      execution.environmentStep nativeApp (.activate alice) = PMF.pure
        { execution with environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment nativeApp, .activate alice⟩] } := by
    simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
      nativeLeaks, alice, watcher, bob, show (0 : Player) ≠ 2 by decide,
      show (0 : Player) ≠ 1 by decide, ↓reduceIte, PMF.pure_map, MessageNetwork.learn_empty]
  rw [activation, PMF.mem_support_pure_iff _ _] at leftMem rightMem
  subst nextLeft nextRight
  exact same

/-- Stop after Alice's actual activation, before consulting her response policy. -/
def bobToAlice (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) : PMF nativeApp.Execution :=
  (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
    [.includeLatest bobPublication bob, .tick, .expire bobPublication, .grant alicePublication]
    (bobSubmission bit submission)).bind fun execution =>
      execution.environmentStep nativeApp (.activate alice)

/-- Uniform over the response contents, private registration, certificates and
all player policies. The proof relies on Alice's actual empty passive sample. -/
theorem wrong_address_alice_input (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication)
    (next : nativeApp.Execution) (supported : next ∈ (bobToAlice players bit submission).support) :
    (next.recall alice, next.observe nativeApp alice) =
      ((beforeAlice bit false).recall alice, (beforeAlice bit false).observe nativeApp alice) := by
  obtain ⟨granted, grantMem, activated⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  rw [runInteractionPlan, wrong_address_inclusion players bit submission wrong,
    PMF.pure_bind] at grantMem
  have inactive (command : EnvironmentCommand nativeGraph) :
      (ReactiveApplication.Command.application command).actor? nativeApp = none := rfl
  have resume : nativeApp.resume players none = PMF.pure := rfl
  simp only [runInteractionPlan, interactionStep, interactionInstruction,
    PMF.pure_bind, ReactiveApplication.dispatch, inactive,
    resume, PMF.bind_pure] at grantMem
  obtain ⟨ticked, tickMem, afterTick⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ grantMem)
  obtain ⟨expired, expiryMem, grantMem⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ afterTick)
  have includedSame : SameAlice (waitExecution (bobSubmission bit submission))
      (silentBobIncluded bit) := same_alice_submission bit submission
  have tickedSame := same_alice_maintenance _ _ ticked (silentBobTicked bit) .advanceClock
    (by intro event impossible; cases impossible) includedSame tickMem
    (by rw [silent_bob_tick]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have expiredSame := same_alice_maintenance _ _ expired (silentBobExpired bit)
    (.expire bobPublication) (by intro event impossible; cases impossible) tickedSame expiryMem
    (by rw [silent_bob_expiry]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have grantedSame := same_alice_maintenance expired (afterBob bit false) granted
    (grantedAlice bit false) (.grant alicePublication)
    (by intro event impossible; cases impossible) expiredSame grantMem
    (by rw [grant_alice]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have finalSame := same_alice_activation granted (grantedAlice bit false) next
    (beforeAlice bit false) grantedSame activated
    (by rw [activate_alice]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact Prod.ext finalSame.2.1 finalSame.2.2

theorem wrong_address_alice_input_law (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication) :
    (bobToAlice players bit submission).map
      (fun next => (next.recall alice, next.observe nativeApp alice)) =
        PMF.pure ((beforeAlice bit false).recall alice,
          (beforeAlice bit false).observe nativeApp alice) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro observed supported
  obtain ⟨next, reached, rfl⟩ := PMF.support_map .. ▸ supported
  exact wrong_address_alice_input players bit submission wrong next reached

end Vegas.Examples.MonitoredGuessing.Restricted
