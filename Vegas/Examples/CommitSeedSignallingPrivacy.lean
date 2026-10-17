/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingContract
import Interaction.ReactivePolicyInvariant
import Interaction.ReactiveTrafficIdentity
import Vegas.Pending.PhaseSeedEmissionPersistence

/-! # Original packet provenance for the private-seed service -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem runRounds_recall_mono (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (first last : app.Execution)
    (supported : last ∈ (app.runRounds selected players count first).support) :
    ∀ owner, first.recall owner ⊆ last.recall owner := by
  let property : app.Execution → Prop := fun current =>
    ∀ owner, first.recall owner ⊆ current.recall owner
  have invariant : app.PolicyInvariant players property := by
    constructor
    · intro current actor action valid _selected owner
      exact List.Subset.trans (valid owner)
          (app.respond_recall_mono current actor owner action)
    · intro current next command valid reached owner
      rw [app.environmentStep_recall current next command reached]
      exact valid owner
  exact invariant.runRounds selected count first last (fun _ => List.Subset.refl _) supported

theorem pendingCommand_inclusion (chosen : MessageId Player)
    (view : app.EnvironmentView) (identifier : MessageId Player)
    (selected : pendingCommand chosen view = .include identifier) : chosen = identifier := by
  unfold pendingCommand at selected
  split at selected
  · exact ReactiveApplication.Command.include.inj selected
  · cases selected

theorem lateCommand_inclusion (owner : Player) (seed : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (identifier : MessageId Player)
    (selected : lateCommand owner seed clock past view = .include identifier) :
    lateClock owner seed = clock ∧ ∃ message,
      (clock, message) ∈ (PhaseSeedScheduler.localInput runtime leaks
        (originalCoordinate owner) owner past view).emissions ∧ message.id = identifier := by
  unfold lateCommand at selected
  split at selected
  · rename_i eligible
    split at selected
    · cases selected
    · rename_i emitted found
      have member := List.mem_of_find?_eq_some found
      have clockEq : emitted.1 = clock := by
        have predicate := List.find?_some found
        exact of_decide_eq_true predicate
      refine ⟨eligible.2, emitted.2, ?_, ?_⟩
      · have pairEq : emitted = (clock, emitted.2) := Prod.ext clockEq rfl
        exact pairEq ▸ member
      · exact pendingCommand_inclusion emitted.2.id view identifier selected
  · cases selected

theorem earlyCommand_inclusion (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (identifier : MessageId Player)
    (selected : earlyCommand owner past view = .include identifier) :
    ∃ entry message, past[2]? = some entry ∧ message ∈ entry.beforeView.network.inputs ∧
      message.sender = owner ∧ message.payload.attempt = originalAttempt ∧
        message.id = identifier := by
  unfold earlyCommand at selected
  split at selected
  · cases selected
  · rename_i entry snapshot
    split at selected
    · cases selected
    · rename_i message found
      have correct : message.sender = owner ∧ message.payload.attempt = originalAttempt := by
        have predicate := List.find?_some found
        exact of_decide_eq_true predicate
      exact ⟨entry, message, snapshot, List.mem_of_find?_eq_some found, correct.1, correct.2,
        pendingCommand_inclusion message.id view identifier selected⟩

/-- A retained original true receipt has a genuine earlier original-namespace
inclusion under the same initialized seed and the same actual raw responses.
The selected action is the real command table, not a supplied delivery law. -/
theorem original_binding_accepted_boundary (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner)
      owner execution) :
    ∃ (prior : app.Execution) (native : PhaseRuntimeState graph) (used : Nat),
      Nonempty ((app.protocol initial horizon (family seeds)).Trace
        (some ⟨horizon - used, none, prior⟩)) ∧
      prior.environmentRecall.length = used ∧
      prior.application.attempt = originalAttempt ∧
      prior.environmentRecall <+: execution.environmentRecall ∧
      PhaseSeedScheduler.WordRecall runtime leaks prior ∧
      (∀ coordinate owner,
        (PhaseSeedScheduler.localInput runtime leaks coordinate owner prior.environmentRecall
          (prior.observeEnvironment app)).emissions <+:
        (PhaseSeedScheduler.localInput runtime leaks coordinate owner execution.environmentRecall
          (execution.observeEnvironment app)).emissions) ∧
      ∃ message ∈ prior.network.inputs,
        message.sender = owner ∧ message.payload.attempt = originalAttempt ∧
        message.payload.packet.call.event? graph = some (bindingEvent owner) ∧
        prior.network.lookup message.id = some message ∧
        prior.application.handle runtime message = some native ∧
        originalCommand seeds used prior.environmentRecall
          (prior.observeEnvironment app) = .include message.id := by
  obtain ⟨message, input, sender, attempt, event, received⟩ := accepted
  have roundSupport := rawMenu.roundSupported_uniform initial horizon (family seeds) trace
  have initialized := roundSupport.2
  rw [ReactiveApplication.roundsFrom, PMF.support_bind] at initialized
  obtain ⟨state, stateSupport, initialized⟩ := Set.mem_iUnion₂.mp initialized
  rw [initial_eq_pure, PMF.mem_support_pure_iff] at stateSupport
  subst state
  obtain ⟨used, rest, prior, middle, length, priorSupported, unreceived, chosen, moved,
    nowReceived, future⟩ := app.runRounds_accepting_receipt_boundary (family seeds)
      rawMenu.uniformResponses execution.environmentRecall.length initialExecution execution
        message.id (by exact List.not_mem_nil) initialized received
  have within : used ≤ horizon := by
    have accounted := roundSupport.1
    change execution.environmentRecall.length + remaining = horizon at accounted
    omega
  have priorFrom : prior ∈
      (app.roundsFrom initial (family seeds) rawMenu.uniformResponses used).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialState, by rw [initial_eq_pure]; simp, priorSupported⟩
  obtain ⟨priorTrace⟩ := app.raw_trace_roundsFrom initial horizon (family seeds)
    rawMenu.uniformResponses used within prior priorFrom
  have priorCount := app.roundsFrom_recall initial (family seeds) rawMenu.uniformResponses
    used prior priorFrom
  have priorWord := PhaseSeedScheduler.runRounds_wordRecall runtime leaks (family seeds)
    rawMenu.uniformResponses used initialExecution prior
      (PhaseSeedScheduler.initial_wordRecall runtime leaks initialState) priorSupported
  have firstRound : middle ∈ (app.round (family seeds) rawMenu.uniformResponses prior).support := by
    rw [ReactiveApplication.round, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨.include message.id, chosen, ?_⟩
    change middle ∈ ((prior.environmentStep app (.include message.id)).bind PMF.pure).support
    simpa only [PMF.bind_pure] using moved
  have suffix : execution ∈
      (app.runRounds (family seeds) rawMenu.uniformResponses (rest + 1) prior).support := by
    change execution ∈ ((app.round (family seeds) rawMenu.uniformResponses prior).bind
      (app.runRounds (family seeds) rawMenu.uniformResponses rest)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨middle, firstRound, future⟩
  obtain ⟨appended, envRecall, _count⟩ := app.runRounds_environmentRecall_append (family seeds)
    rawMenu.uniformResponses (rest + 1) prior execution suffix
  have envPrefix : prior.environmentRecall <+: execution.environmentRecall :=
    ⟨appended, envRecall.symm⟩
  have emissionPrefix := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks
    (family seeds) rawMenu.uniformResponses (rest + 1) prior execution priorWord suffix
  have includeEq := moved
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.mem_support_pure_iff] at includeEq
  cases found : prior.network.lookup message.id with
  | none =>
      have unchanged : middle.receipts = prior.receipts := by
        rw [includeEq]
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found]
      exact (unreceived (unchanged ▸ nowReceived)).elim
  | some actual =>
      have named : actual.id = message.id := by
        have predicate := List.find?_some found
        exact of_decide_eq_true predicate
      have actualInput := (app.retained_envelopes_mem_inputs prior
        (app.history_provenance initial horizon (family seeds) priorTrace)
        (app.history_inputRecall initial horizon (family seeds) priorTrace)).lookup
          message.id actual found
      have recalled := runRounds_recall_mono (family seeds) rawMenu.uniformResponses rest
        middle execution future
      have sameRecall : middle.recall = prior.recall := by
        rw [includeEq]
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found]
      have actualOutput : actual ∈ app.outputs (prior.recall actual.sender) := by
        rw [← app.history_inputRecall initial horizon (family seeds) priorTrace actual.sender]
        exact List.mem_filter.mpr ⟨actualInput, by simp only [decide_true]⟩
      obtain ⟨entry, retained, emitted⟩ := List.mem_filterMap.mp actualOutput
      have finalOutput : actual ∈ app.outputs (execution.recall actual.sender) := by
        apply List.mem_filterMap.mpr
        refine ⟨entry, ?_, emitted⟩
        apply recalled actual.sender
        rw [sameRecall]
        exact retained
      have raw := rawMenu.toRawTrace initial horizon (family seeds) trace
      rw [← app.history_inputRecall initial horizon (family seeds) raw actual.sender] at finalOutput
      have sameMessage := app.input_identifier_injective_history initial horizon (family seeds)
        ⟨remaining, none, execution⟩ raw actual message
          (List.mem_filter.mp finalOutput).1 input named
      subst actual
      have newReceipt : (message.id, true) ∈ prior.receipts ++
          [(message.id, (prior.application.handle runtime message).isSome)] := by
        rw [includeEq] at nowReceived
        change (message.id, true) ∈ prior.receipts ++
          [(message.id, (app.handle prior.application message).isSome)]
        simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found] using nowReceived
      rcases List.mem_append.mp newReceipt with old | fresh
      · exact (unreceived old).elim
      · have valid : (prior.application.handle runtime message).isSome = true :=
          (congrArg Prod.snd (List.mem_singleton.mp fresh)).symm
        obtain ⟨native, handled⟩ := Option.isSome_iff_exists.mp valid
        have original : prior.application.attempt = originalAttempt := by
          exact (PhaseRuntimeState.handle_attempt_eq runtime prior.application native message
            handled).symm.trans attempt
        have selected : originalCommand seeds used prior.environmentRecall
            (prior.observeEnvironment app) = .include message.id := by
          have decision := (PMF.mem_support_pure_iff _ _).mp chosen
          rw [choose_original seeds prior.environmentRecall (prior.observeEnvironment app)
            original, priorCount] at decision
          exact decision.symm
        exact ⟨prior, native, used, ⟨priorTrace⟩, priorCount, original, envPrefix, priorWord,
          (fun coordinate owner => emissionPrefix owner coordinate), message, actualInput,
          sender, attempt, event, found, handled, selected⟩

end Vegas.Examples.CommitSeedSignalling
