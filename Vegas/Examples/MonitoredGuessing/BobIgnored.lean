/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.BobContinuationTrace
import Vegas.Examples.MonitoredGuessing.EnforcementPayoffs

/-! # Wrong-address receiver traffic retains the source continuation

The pending envelope is absent from Alice's actual input. Owner-local final
handling preserves the terminal results, and reserved inclusion for Alice
cannot publish a Bob envelope. Thus the financial comparison also retains Bob's
clear ledger liability.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private theorem owner_view_results (left right : nativeApp.Execution)
    (same : left.application.playerView alice = right.application.playerView alice) :
    nativeResults left.application.config = nativeResults right.application.config := by
  have publication (reference : EventGraph.FieldRef nativeGraph.layout (.publication .bool)) :
      reference.get? left.application.config.store =
        reference.get? right.application.config.store := by
      have stored := congrArg (fun view : PlayerView nativeGraph =>
        reference.get? view.observation.store) same
      change reference.get? (nativeGraph.playerStore alice left.application.config.store) =
        reference.get? (nativeGraph.playerStore alice right.application.config.store) at stored
      simpa only [reference.get?_playerStore alice _ trivial] using stored
  change Results.mk _ _ = Results.mk _ _
  rw [publication alicePublicationRef, publication bobPublicationRef]

theorem wrong_address_final_results (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (available : (⟨some (.submit submission)⟩ : nativeApp.Action) ∈
      nativeMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication)
    (next : nativeApp.Execution) (supported : next ∈ (bobToAlice players bit submission).support)
    (response : nativeApp.Action) :
    nativeResults (finalResponseExecution next response).application.config =
      nativeResults
        (finalResponseExecution (beforeAlice bit false) response).application.config := by
  have input := wrong_address_alice_input players bit submission wrong next supported
  apply owner_view_results
  exact final_response_owner_local next (beforeAlice bit false) response
    (wrong_address_alice_local players bit submission available wrong next supported)
    (before_alice_false_local bit) (congrArg Prod.fst input) (congrArg Prod.snd input)

private theorem response_bob_audit (execution : nativeApp.Execution) (who : Player)
    (response : nativeApp.Action) :
    Conformance.bobLedgerViolation (execution.respond nativeApp who response) =
      Conformance.bobLedgerViolation execution := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => rfl
      | replay id =>
          simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay]
          split <;> rfl

theorem final_reserved_bob_audit (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution)
    (supported : next ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest alicePublication alice) execution).support) :
    Conformance.bobLedgerViolation next = Conformance.bobLedgerViolation execution := by
  rw [nativeRuntime.interaction_includeLatest_environment] at supported
  rcases nativeRuntime.reactiveLatest_wait_or_owned nativeLeaks alicePublication alice
      (execution.observeEnvironment nativeApp) with wait | ⟨id, authored, selected⟩
  · rw [wait] at supported
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at supported
    cases FinDist.mem_support_pure.mp supported
    rfl
  · rw [selected] at supported
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at supported
    cases FinDist.mem_support_pure.mp supported
    change ledgerViolation bob Conformance.bobPacketPermitted
      (execution.includePending nativeApp id).network.ledger = _
    rw [nativeApp.includePending_network]
    cases found : execution.network.lookup id with
    | none => rw [MessageNetwork.includePending, found]; rfl
    | some message =>
        have found' : execution.network.pending.find? (fun packet => packet.id = id) =
            some message := found
        have matching : message.id = id := by simpa using List.find?_some found'
        have other : message.sender ≠ bob := by
          change message.id.1 ≠ bob
          rw [matching, authored]
          decide
        simp only [MessageNetwork.includePending, found, ledgerViolation, List.any_append,
          List.any_cons, other, decide_false, Bool.false_and, List.any_nil, Bool.or_self,
          Bool.or_false, Conformance.bobLedgerViolation]

theorem final_response_bob_audit (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (response : nativeApp.Action)
    (final : nativeApp.Execution)
    (supported : final ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      resolutionTail (execution.respond nativeApp alice response)).support) :
    Conformance.bobLedgerViolation final = Conformance.bobLedgerViolation execution := by
  obtain ⟨included, includedMem, tailMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  exact (Enforcement.clock_tail_bob_audit players included final tailMem).trans
    ((final_reserved_bob_audit players (execution.respond nativeApp alice response)
      included includedMem).trans (response_bob_audit execution alice response))

theorem wrong_address_final_bob_clear (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication)
    (next : nativeApp.Execution) (supported : next ∈ (bobToAlice players bit submission).support)
    (response : nativeApp.Action) :
    Conformance.bobLedgerViolation (finalResponseExecution next response) = false := by
  have input := wrong_address_alice_input players bit submission wrong next supported
  have ledger : next.network.ledger = (beforeAlice bit false).network.ledger :=
    congrArg (fun input : List nativeApp.PlayerEntry × nativeApp.PlayerView =>
      input.2.messages.ledger) input
  have clear : Conformance.bobLedgerViolation next = false := by
    rw [Conformance.bobLedgerViolation, ledger]
    exact Enforcement.before_alice_bob_clear bit false
  apply (final_response_bob_audit players next response _ ?_).trans clear
  rw [final_response_law]
  exact FinDist.mem_support_pure.mpr rfl

theorem wrong_address_final_payoff_law (table : PayoffTable)
    (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (available : (⟨some (.submit submission)⟩ : nativeApp.Action) ∈
      nativeMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication)
    (next : nativeApp.Execution) (supported : next ∈ (bobToAlice players bit submission).support)
    (disclose : Bool) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      (next.respond nativeApp alice (choiceAction alicePublication aliceHandle bit disclose))).map
        (fun final => (nativeResults final.application.config,
          Enforcement.executionUtility table final bob)) =
      FinDist.pure (sourceResults (finalConfig bit false disclose).state,
        (table (sourceResults (finalConfig bit false disclose).state) bob : ℝ)) := by
  let response := choiceAction alicePublication aliceHandle bit disclose
  have canonical := Enforcement.alice_service_payoff_law table players bit false disclose
  rw [final_response_law, FinDist.map_pure] at canonical
  have canonicalPair := FinDist.mem_support_pure.mp
    (canonical ▸ FinDist.mem_support_pure.mpr rfl)
  have result := (wrong_address_final_results players bit submission available wrong next supported
    response).trans (congrArg Prod.fst canonicalPair)
  have clear := wrong_address_final_bob_clear players bit submission wrong next supported response
  rw [final_response_law, FinDist.map_pure]
  change FinDist.pure (_, _) = FinDist.pure (_, _)
  congr 1
  apply Prod.ext result
  rw [Enforcement.bob_utility]
  change (table (nativeResults (finalResponseExecution next response).application.config) bob : ℝ) -
    (Enforcement.deposit table bob : ℝ) *
      Conformance.bobLedgerLiability (finalResponseExecution next response) = _
  rw [Conformance.bobLedgerLiability, clear, ite_eq_right Bool.false_ne_true, mul_zero, sub_zero,
    result]

/-- Expand the existing service at Alice's next response without introducing
another protocol or modifying any observation. -/
theorem bob_continuation_evaluation (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      (bobSubmission bit submission) =
    (bobToAlice players bit submission).bind (fun next =>
      (players alice (next.recall alice) (next.observe nativeApp alice)).bind fun response =>
        nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
          (next.respond nativeApp alice response)) := by
  change nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
      .grant alicePublication] ++ [.player alice] ++ resolutionTail) _ = _
  rw [runInteractionPlan_append, runInteractionPlan_append]
  have step (execution : nativeApp.Execution) :
      nativeRuntime.interactionStep nativeLeaks players nativeNetwork (.player alice) execution =
        (execution.environmentStep nativeApp (.activate alice)).bind (fun next =>
          (players alice (next.recall alice) (next.observe nativeApp alice)).map
            (next.respond nativeApp alice)) := by
    rw [interactionStep, interactionInstruction, FinDist.pure_bind]
    rfl
  simp only [bobToAlice, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro execution _
  rw [runInteractionPlan]
  simp only [runInteractionPlan, FinDist.bind_pure, step, FinDist.bind_bind, FinDist.bind_map]

/-- Wrong-address traffic has exactly the silent source continuation's game
results and receiver payoff for every mixed legal Alice response. -/
theorem wrong_address_continuation_payoff_law (table : PayoffTable)
    (players : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (available : (⟨some (.submit submission)⟩ : nativeApp.Action) ∈
      nativeMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication)
    (choices : FinDist Bool)
    (aliceChoice : players alice ((beforeAlice bit false).recall alice)
      ((beforeAlice bit false).observe nativeApp alice) =
        choices.map (choiceAction alicePublication aliceHandle bit)) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      (bobSubmission bit submission)).map
        (fun final => (nativeResults final.application.config,
          Enforcement.executionUtility table final bob)) =
      choices.map (fun disclose => (sourceResults (finalConfig bit false disclose).state,
        (table (sourceResults (finalConfig bit false disclose).state) bob : ℝ))) := by
  rw [bob_continuation_evaluation, FinDist.map_bind]
  trans (bobToAlice players bit submission).bind (fun _ =>
    choices.map (fun disclose => (sourceResults (finalConfig bit false disclose).state,
      (table (sourceResults (finalConfig bit false disclose).state) bob : ℝ))))
  · apply FinDist.bind_congr
    intro next supported
    have input := wrong_address_alice_input players bit submission wrong next supported
    have recall : next.recall alice = (beforeAlice bit false).recall alice :=
      congrArg Prod.fst input
    have observation : next.observe nativeApp alice =
        (beforeAlice bit false).observe nativeApp alice := congrArg Prod.snd input
    rw [recall, observation, aliceChoice, FinDist.bind_map, FinDist.map_bind]
    rw [FinDist.map_eq_bind]
    apply FinDist.bind_congr
    intro disclose _
    exact wrong_address_final_payoff_law table players bit submission available wrong next supported
      disclose
  · exact FinDist.bind_const _ _

theorem silence_continuation_payoff_law (table : PayoffTable)
    (players : Player → nativeApp.Policy) (bit : Bool) (choices : FinDist Bool)
    (aliceChoice : players alice ((beforeAlice bit false).recall alice)
      ((beforeAlice bit false).observe nativeApp alice) =
        choices.map (choiceAction alicePublication aliceHandle bit)) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob nativeSilent)).map
        (fun final => (nativeResults final.application.config,
          Enforcement.executionUtility table final bob)) =
      choices.map (fun disclose => (sourceResults (finalConfig bit false disclose).state,
        (table (sourceResults (finalConfig bit false disclose).state) bob : ℝ))) := by
  change (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork _
    ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true false))).map
      _ = _
  rw [runInteractionPlan_append, bob_to_alice, aliceChoice, FinDist.map_comp,
    FinDist.bind_map, FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro disclose _
  have law := Enforcement.alice_service_payoff_law table players bit false disclose
  have observed := congrArg (fun law : FinDist (Results × (Player → ℝ)) =>
    law.map (fun result => (result.1, result.2 bob))) law
  simpa only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] using observed

/-- A fixed legal silence action compares with every ignored submission.
The two arbitrary continuations need agree only on the mixed legal action at
Alice's matched information, as required by the retained-profile relation. -/
theorem wrong_address_compared_with_silence (table : PayoffTable)
    (rawPlayers legalPlayers : Player → nativeApp.Policy) (bit : Bool)
    (submission : WitnessedSubmission nativeGraph)
    (available : (⟨some (.submit submission)⟩ : nativeApp.Action) ∈
      nativeMenu.actions bob [] ((quietBob bit).observe nativeApp bob))
    (wrong : submission.call.packet.event? nativeGraph ≠ some bobPublication)
    (choices : FinDist Bool)
    (rawChoice : rawPlayers alice ((beforeAlice bit false).recall alice)
      ((beforeAlice bit false).observe nativeApp alice) =
        choices.map (choiceAction alicePublication aliceHandle bit))
    (legalChoice : legalPlayers alice ((beforeAlice bit false).recall alice)
      ((beforeAlice bit false).observe nativeApp alice) =
        choices.map (choiceAction alicePublication aliceHandle bit)) :
    (nativeRuntime.runInteractionPlan nativeLeaks rawPlayers nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      (bobSubmission bit submission)).map
        (fun final => (nativeResults final.application.config,
          Enforcement.executionUtility table final bob)) =
    (nativeRuntime.runInteractionPlan nativeLeaks legalPlayers nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob nativeSilent)).map
        (fun final => (nativeResults final.application.config,
          Enforcement.executionUtility table final bob)) := by
  rw [wrong_address_continuation_payoff_law table rawPlayers bit submission available wrong
    choices rawChoice, silence_continuation_payoff_law table legalPlayers bit choices legalChoice]

end Vegas.Examples.MonitoredGuessing.Restricted
