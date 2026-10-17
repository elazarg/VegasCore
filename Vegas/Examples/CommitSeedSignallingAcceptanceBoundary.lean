/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingDelivery
import Vegas.Examples.CommitSeedSignallingResolvedContinuation
import Interaction.ReactiveRecordedRounds

/-! # Actual first accepting binding after a fixed physical prefix -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- A new accepting binding is witnessed along this very continuation,
including its original prefix, actual scheduler command and real handler. -/
theorem continued_binding_acceptance_boundary (selected : app.Scheduler)
    (players : Player → app.Policy) (remaining count : Nat) (before after : app.Execution)
    (trace : (app.protocol initial horizon selected).Trace (some ⟨remaining, none, before⟩))
    (bounded : count ≤ remaining)
    (reached : after ∈ (app.runRounds selected players count before).support)
    (owner : Player)
    (unaccepted : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner before)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner after) :
    ∃ (used : Nat) (prior : app.Execution) (native : PhaseRuntimeState graph)
      (message : Message Player app.Payload),
      used < count ∧
      prior ∈ (app.runRounds selected players used before).support ∧
      Nonempty ((app.protocol initial horizon selected).Trace
        (some ⟨remaining - used, none, prior⟩)) ∧
      prior.application.attempt = originalAttempt ∧
      message.sender = owner ∧
      message.payload.attempt = originalAttempt ∧
      prior.network.lookup message.id = some message ∧
      prior.application.handle runtime message = some native ∧
      (.include message.id : app.Command) ∈
        (selected prior.environmentRecall (prior.observeEnvironment app)).support := by
  classical
  obtain ⟨afterTrace⟩ := app.raw_trace_runRounds initial horizon selected players
    (remaining - count) count before after (by
      simpa only [Nat.sub_add_cancel bounded] using trace) reached
  have inputPrefix := inputs_prefix_of_rounds selected players count
    ⟨remaining, none, before⟩ ⟨remaining - count, none, after⟩ trace afterTrace reached
  obtain ⟨message, input, sender, attempt, event, received⟩ := accepted
  have unreceived : (message.id, true) ∉ before.receipts := by
    intro old
    have identifiers := app.receipt_identifiers_history initial horizon selected
      ⟨remaining, none, before⟩ trace
    have published : message.id ∈ before.network.ledger.map Message.id := by
      rw [← identifiers]
      exact List.mem_map.mpr ⟨(message.id, true), old, rfl⟩
    obtain ⟨prior, ledger, sameId⟩ := List.mem_map.mp published
    have priorInput := app.ledger_subset_inputs_history initial horizon selected
      ⟨remaining, none, before⟩ trace ledger
    have same := app.input_identifier_injective_history initial horizon selected
      ⟨remaining - count, none, after⟩ afterTrace prior message
      (inputPrefix.sublist.subset priorInput) input sameId
    subst prior
    exact unaccepted ⟨message, priorInput, sender, attempt, event, old⟩
  obtain ⟨used, rest, prior, middle, length, priorSupported, unreceivedPrior, chosen,
    moved, nowReceived, future⟩ := app.runRounds_accepting_receipt_boundary selected players
      count before after message.id unreceived reached received
  have usedBound : used ≤ remaining := by omega
  obtain ⟨priorTrace⟩ := app.raw_trace_runRounds initial horizon selected players
    (remaining - used) used before prior (by
      simpa only [Nat.sub_add_cancel usedBound] using trace) priorSupported
  have firstRound : middle ∈ (app.round selected players prior).support := by
    rw [ReactiveApplication.round, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨.include message.id, chosen, ?_⟩
    change middle ∈ ((prior.environmentStep app (.include message.id)).bind PMF.pure).support
    simpa only [PMF.bind_pure] using moved
  have suffix : after ∈ (app.runRounds selected players (rest + 1) prior).support := by
    change after ∈ ((app.round selected players prior).bind
      (app.runRounds selected players rest)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨middle, firstRound, future⟩
  have priorInputs := inputs_prefix_of_rounds selected players (rest + 1)
    ⟨remaining - used, none, prior⟩ ⟨remaining - count, none, after⟩
    priorTrace afterTrace suffix
  have includeEq := moved
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff] at includeEq
  cases found : prior.network.lookup message.id with
  | none =>
      have unchanged : middle.receipts = prior.receipts := by
        rw [includeEq]
        simp only [ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found]
      exact (unreceivedPrior (unchanged ▸ nowReceived)).elim
  | some actual =>
      have named : actual.id = message.id := by
        have predicate := List.find?_some found
        exact of_decide_eq_true predicate
      have actualInput := (app.retained_envelopes_mem_inputs prior
        (app.history_provenance initial horizon selected priorTrace)
        (app.history_inputRecall initial horizon selected priorTrace)).lookup
          message.id actual found
      have same := app.input_identifier_injective_history initial horizon selected
        ⟨remaining - count, none, after⟩ afterTrace actual message
        (priorInputs.sublist.subset actualInput) input named
      subst actual
      have newReceipt : (message.id, true) ∈ prior.receipts ++
          [(message.id, (prior.application.handle runtime message).isSome)] := by
        rw [includeEq] at nowReceived
        change (message.id, true) ∈ prior.receipts ++
          [(message.id, (app.handle prior.application message).isSome)]
        simpa only [ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found] using nowReceived
      rcases List.mem_append.mp newReceipt with old | fresh
      · exact (unreceivedPrior old).elim
      · have valid : (prior.application.handle runtime message).isSome = true :=
          (congrArg Prod.snd (List.mem_singleton.mp fresh)).symm
        obtain ⟨native, handled⟩ := Option.isSome_iff_exists.mp valid
        have unresolved := PhaseRuntimeState.handle_event_unresolved runtime
          prior.application native message (bindingEvent owner) event handled
        change ¬ (⟨message.payload.attempt, bindingEvent owner⟩ :
          CommitAttemptEvent graph).Resolved prior.application at unresolved
        rw [attempt] at unresolved
        have request := original_binding_request_of_unresolved selected
          ⟨remaining - used, none, prior⟩ priorTrace owner unresolved
        exact ⟨used, prior, native, message, by omega, priorSupported, ⟨priorTrace⟩,
          request.1.symm, sender, attempt, found, handled, chosen⟩

/-- Once Alice's late slots have passed, an empty early snapshot rules out
any new original Alice acceptance along the actual physical continuation. -/
theorem alice_binding_unaccepted_after_late (seed : Seeds)
    (players : Player → app.Policy) (remaining count : Nat) (before after : app.Execution)
    (trace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, before⟩))
    (bounded : count ≤ remaining)
    (reached : after ∈ (app.runRounds (family seed) players count before).support)
    (late : 12 ≤ before.environmentRecall.length)
    (empty : ∀ entry, before.environmentRecall[2]? = some entry →
      ∀ message ∈ entry.beforeView.network.inputs, message.sender ≠ alice)
    (unaccepted : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate alice)
      alice before) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate alice) alice after := by
  intro accepted
  obtain ⟨used, prior, native, packet, _within, priorSupported, ⟨priorTrace⟩, original,
    sender, _attempt, _found, _handled, chosen⟩ := continued_binding_acceptance_boundary
      (family seed) players remaining count before after trace bounded reached alice
      unaccepted accepted
  have selected : originalCommand seed prior.environmentRecall.length prior.environmentRecall
      (prior.observeEnvironment app) = .include packet.id := by
    have command := (PMF.mem_support_pure_iff _ _).mp chosen
    rw [choose_original seed prior.environmentRecall (prior.observeEnvironment app) original]
      at command
    exact command.symm
  have length := app.runRounds_environmentRecall_length (family seed) players used before
    prior priorSupported
  rcases original_include_cases seed _ _ _ packet.id selected with early | later
  · obtain ⟨source, position, included⟩ := early
    rcases position with ⟨_owner, early⟩ | ⟨rfl, _position⟩
    · omega
    · obtain ⟨entry, message, snapshot, input, authored, _attempt, _named⟩ :=
        earlyCommand_inclusion alice prior.environmentRecall (prior.observeEnvironment app)
          packet.id included
      obtain ⟨rest, recalled, _count⟩ := app.runRounds_environmentRecall_append (family seed)
        players used before prior priorSupported
      have snapshotBefore : before.environmentRecall[2]? = some entry := by
        rw [recalled, List.getElem?_append_left (by omega)] at snapshot
        exact snapshot
      exact empty entry snapshotBefore message input authored
  · obtain ⟨source, clock, position, included⟩ := later
    rcases position with ⟨_owner, position⟩ | ⟨rfl, _position⟩
    · rcases position with early | early <;> omega
    · obtain ⟨_eligible, message, emitted, named⟩ := lateCommand_inclusion bob
        (seed.2 (originalAddress bob)) clock prior.environmentRecall
        (prior.observeEnvironment app) packet.id included
      have authored := localInput_sender (originalCoordinate bob) bob
        prior.environmentRecall (prior.observeEnvironment app) clock message emitted
      have owners : bob = alice := authored.symm.trans
        ((congrArg Prod.fst named).trans sender)
      exact (by decide : bob ≠ alice) owners

end Vegas.Examples.CommitSeedSignalling
