/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingUnresolved
import Interaction.ReactiveTrafficContinuation

/-! # No new accepting original receipt after physical resolution -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

theorem inputs_prefix_of_rounds (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (before after : app.Control)
    (beforeTrace : (app.protocol initial horizon selected).Trace (some before))
    (afterTrace : (app.protocol initial horizon selected).Trace (some after))
    (reached : after.execution ∈ (app.runRounds selected players count before.execution).support) :
    before.execution.network.inputs <+: after.execution.network.inputs := by
  have kept := (app.executionTraffic_runRounds selected players count before.execution
    after.execution reached).map ReactiveApplication.TrafficRecord.envelope
  have beforeInputs := app.stateTraffic_inputs initial horizon selected beforeTrace
  have afterInputs := app.stateTraffic_inputs initial horizon selected afterTrace
  change (app.executionTraffic before.execution).map ReactiveApplication.TrafficRecord.envelope =
    before.execution.network.inputs at beforeInputs
  change (app.executionTraffic after.execution).map ReactiveApplication.TrafficRecord.envelope =
    after.execution.network.inputs at afterInputs
  rwa [beforeInputs, afterInputs] at kept

/-- Resolution cannot turn an unaccepted original binding into an accepted
one, even through arbitrary raw responses, retries and later phases. -/
theorem resolved_unaccepted_binding_stays_unaccepted (selected : app.Scheduler)
    (players : Player → app.Policy) (remaining count : Nat) (before after : app.Execution)
    (trace : (app.protocol initial horizon selected).Trace (some ⟨remaining, none, before⟩))
    (bounded : count ≤ remaining)
    (reached : after ∈ (app.runRounds selected players count before).support)
    (owner : Player)
    (resolved : (originalCoordinate owner).Resolved before.application)
    (unaccepted : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner before) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after := by
  classical
  obtain ⟨afterTrace⟩ := app.raw_trace_runRounds initial horizon selected players
    (remaining - count) count before after (by
      simpa only [Nat.sub_add_cancel bounded] using trace) reached
  have inputPrefix := inputs_prefix_of_rounds selected players count
    ⟨remaining, none, before⟩ ⟨remaining - count, none, after⟩ trace afterTrace reached
  intro accepted
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
  obtain ⟨used, rest, prior, middle, length, priorSupported, unreceivedPrior, _chosen, moved,
    nowReceived, future⟩ := app.runRounds_accepting_receipt_boundary selected players
      count before after message.id unreceived reached received
  have usedBound : used ≤ remaining := by omega
  obtain ⟨priorTrace⟩ := app.raw_trace_runRounds initial horizon selected players
    (remaining - used) used before prior (by
      simpa only [Nat.sub_add_cancel usedBound] using trace) priorSupported
  have firstRound : middle ∈ (app.round selected players prior).support := by
    rw [ReactiveApplication.round, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨.include message.id, _chosen, ?_⟩
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
      exact unreceivedPrior (unchanged ▸ nowReceived)
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
        have impossible := CommitAttemptEvent.Resolved.no_request_runRounds runtime leaks
          (originalCoordinate owner) selected players used before prior
          (raw_native_valid selected ⟨remaining, none, before⟩ trace)
          (raw_phase_geometry selected ⟨remaining, none, before⟩ trace).1.adjacent
          resolved priorSupported owner
        exact impossible request

end Vegas.Examples.CommitSeedSignalling
