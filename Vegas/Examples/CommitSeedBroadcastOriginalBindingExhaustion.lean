/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalCalendar
import Vegas.Examples.CommitSeedBroadcastProperPolicy
import Vegas.Pending.PhaseRecordedCountedRequest
import Vegas.Pending.PhaseTimelyResolution
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveProvenance

/-! # Silent resolved episodes in the actual counted service -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem unsent_of_empty_emissions (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (empty : PhaseService.bindingEmissionClocks runtime leaks coordinate owner execution = []) :
    ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have inputRecall := app.history_inputRecall initial horizon (family seeds) raw
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seeds) remaining execution trace
  have emptyWord : (PhaseSeedScheduler.localInput runtime leaks coordinate owner
      execution.environmentRecall (execution.observeEnvironment app)).emissions = [] :=
    List.map_eq_nil_iff.mp empty
  intro message authored named
  have own : message.sender = owner := by
    rw [← inputRecall owner] at authored
    exact of_decide_eq_true (List.mem_filter.mp authored).2
  have input : message ∈ execution.network.inputs := by
    rw [← inputRecall owner] at authored
    exact (List.mem_filter.mp authored).1
  obtain ⟨entry, retained, material, transmitted, emitted, state, known, packet⟩ :=
    (app.history_provenance initial horizon (family seeds) raw).inputs message input
  rw [own] at retained
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  obtain ⟨actual, requested, stamp, actualNamed⟩ := PhaseCount.recorded_material_request runtime
    leaks bounds plan (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon (family seeds) _ compiledTrace owner entry retained
      material transmitted
  have fields : message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event := by
    unfold PhaseCount.event? at named
    obtain ⟨event, eventEq, same⟩ := Option.map_eq_some_iff.mp named
    cases same
    exact ⟨rfl, eventEq⟩
  have exactCall := phase_emit_call state message.sender known material
  change state.emit message.sender known material = message.payload at packet
  have callEq : material.call.packet = message.payload.packet.call :=
    exactCall.symm.trans (congrArg (fun output => output.packet.call) packet)
  have tag := phase_recalled_emission_attempt runtime leaks initial horizon (family seeds) raw
    owner entry retained message emitted
  have sameTag : actual.attempt = coordinate.attempt := stamp.trans (tag.symm.trans fields.1)
  have sameEvent : actual.event = coordinate.event := Option.some.inj
    (actualNamed.symm.trans ((congrArg (Payload.event? graph) callEq).trans fields.2))
  have same : actual = coordinate := by
    cases actual
    cases coordinate
    cases sameTag
    cases sameEvent
    rfl
  rw [same] at requested
  have packetOwn : PhaseSeedScheduler.ownPacket coordinate owner message = true := by
    exact decide_eq_true ⟨own, fields⟩
  let clock := entry.beforeView.application.2.native.clock -
    (entry.beforeView.application.2.native.activatedAt coordinate.event).getD
      entry.beforeView.application.2.native.clock
  have recalledRecord : (clock, entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket coordinate owner)) ∈
      PhaseSeedScheduler.ownerWord runtime leaks coordinate owner (execution.recall owner) := by
    apply List.mem_map.mpr
    refine ⟨entry, List.mem_filter.mpr ⟨retained, decide_eq_true requested⟩, rfl⟩
  have emittedRecord : message ∈ entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket coordinate owner) := by
    rw [emitted]
    exact List.mem_filter.mpr ⟨List.mem_singleton_self _, packetOwn⟩
  have recordedEmission : (clock, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions := by
    rw [PhaseSeedScheduler.localInput_word, words owner coordinate]
    apply List.mem_flatMap.mpr
    exact ⟨_, recalledRecord, List.mem_map.mpr ⟨message, emittedRecord, rfl⟩⟩
  rw [emptyWord] at recordedEmission
  exact List.not_mem_nil recordedEmission

theorem unsent_request_retained_or_expiry (seeds : Seeds) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (app.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate)
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (command : app.Command) (moved : next ∈ (execution.environmentStep app command).support) :
    next.application.SeedRequest owner coordinate ∨
      command = .application (.expire coordinate.event) := by
  classical
  have valid := raw_native_valid (family seeds) _ trace
  rcases environment_request_or_own_resolution runtime leaks
      (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) execution next valid owner
      coordinate request command moved with retained | expiry | included
  · exact Or.inl retained
  · exact Or.inr expiry
  · by_cases retained : next.application.SeedRequest owner coordinate
    · exact Or.inl retained
    obtain ⟨identifier, message, _native, _ready, _action, selected, found, authored, named,
      _accepted, _stepped, _normalized⟩ := included
    have tag : message.payload.attempt = execution.application.attempt := by
      by_contra retired
      have rejected : app.handle execution.application message = none :=
        execution.application.handle_retired runtime message retired
      rw [selected] at moved
      have exactState : next.application =
          (execution.includePending app identifier).application := by
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff] at moved
        have projected := congrArg (fun after : app.Execution => after.application) moved
        change next.application = (execution.includePending app identifier).application at projected
        exact projected
      have unchanged : next.application = execution.application := by
        rw [exactState]
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, rejected, Option.getD_none]
      exact retained (unchanged.symm ▸ request)
    have pending : message ∈ execution.network.pending := List.mem_of_find?_eq_some found
    have input := (app.retained_envelopes_mem_inputs execution
      (app.history_provenance initial horizon (family seeds) trace)
      (app.history_inputRecall initial horizon (family seeds) trace)).pending message pending
    have output : message ∈ app.outputs (execution.recall owner) := by
      rw [← app.history_inputRecall initial horizon (family seeds) trace owner]
      exact List.mem_filter.mpr ⟨input, decide_eq_true authored⟩
    apply False.elim
    apply unsent message output
    simp only [PhaseCount.event?, named, Option.map_some, tag, ← request.1]

private theorem original_word_full (seeds : Seeds) (owner : Player) :
    originalClockWord seeds owner (27 + owner.val) = [0, 2, 3] := by
  unfold originalClockWord
  generalize bitEq : seeds.2 owner = bit
  generalize rankEq : seeds.1.symm owner = rank
  fin_cases owner <;> fin_cases rank <;> cases bit <;> decide

private theorem original_request_loss_clock_word (seeds : Seeds) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (command : app.Command)
    (selected : command ∈ (family seeds execution.environmentRecall
      (execution.observeEnvironment app)).support)
    (moved : next ∈ (execution.environmentStep app command).support)
    (lost : ¬ next.application.SeedRequest owner (originalCoordinate owner)) :
    (originalCoordinate owner).Resolved next.application ∧
      clockWord (originalCoordinate owner) owner next.environmentRecall =
        [0, 2, 3] := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have original : execution.application.attempt = originalAttempt := request.1.symm
  obtain retained | expiry := unsent_request_retained_or_expiry seeds remaining execution next raw
    (originalCoordinate owner) owner request unsent command moved
  · exact (lost retained).elim
  have expiryMoved := moved
  rw [expiry] at expiryMoved
  have chosen : originalCommand seeds execution.environmentRecall.length
      execution.environmentRecall (execution.observeEnvironment app) = command := by
    have actual := (PMF.mem_support_pure_iff _ _).mp selected
    exact (choose_original seeds _ _ original).symm.trans actual.symm
  have position := original_command_expiry seeds owner execution.environmentRecall.length
    execution.environmentRecall (execution.observeEnvironment app) (chosen.trans expiry)
  have resolved := original_expiry_resolves seeds _ raw original owner position next expiryMoved
  have clocks := original_clock_words countedMenu seeds trace owner request
  have notCallback : ¬ PhaseSeedScheduler.callback runtime leaks (originalCoordinate owner) owner
      ⟨execution.observeEnvironment app, command⟩ := by
    intro callback
    rw [expiry] at callback
    cases callback.1
  refine ⟨resolved, ?_⟩
  rw [app.environmentStep_environmentRecall execution next command moved, clockWord_snoc,
    ite_eq_right notCallback, List.append_nil, clocks]
  rw [position]
  exact original_word_full seeds owner

private theorem original_silent_progress (seeds : Seeds) :
    ∀ {state} (_trace : (countedMenu.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => ∀ owner,
        (∀ message ∈ app.outputs (current.execution.recall owner),
          PhaseCount.event? message.payload ≠ some (originalCoordinate owner)) →
        current.execution.application.SeedRequest owner (originalCoordinate owner) ∨
          ((originalCoordinate owner).Resolved current.execution.application ∧
            clockWord (originalCoordinate owner) owner
              current.execution.environmentRecall =
              [0, 2, 3])) := by
  classical
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rw [initial, PMF.mem_support_pure_iff] at supported
          subst state
          intro owner _unsent
          left
          change initialState.SeedRequest owner (originalCoordinate owner)
          have valid := (PhaseRuntimeState.initial_invariant plan
            (encodeInputs (Env.empty (CellVal simpleExpr)))).1
          apply (initialState.requests_publicView valid owner (originalCoordinate owner)).mp
          exact initial_bindings_ready owner
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          have raw := countedMenu.toRawTrace initial horizon (family seeds) prior
          have valid := raw_native_valid (family seeds) _ raw
          have ordered := (raw_phase_geometry (family seeds) _ raw).1.adjacent
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              intro owner unsent
              have beforeUnsent : ∀ message ∈ app.outputs (execution.recall owner),
                  PhaseCount.event? message.payload ≠ some (originalCoordinate owner) := by
                intro message output
                obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
                exact unsent message (List.mem_filterMap.mpr ⟨entry,
                  (app.respond_recall_prefix execution actor owner
                    ((joint actor).getD ⟨none⟩)).subset member, emitted⟩)
              rcases ih owner beforeUnsent with request | ⟨resolved, clocks⟩
              · exact Or.inl (respond_request runtime leaks execution actor _ owner
                  (originalCoordinate owner) request)
              · right
                refine ⟨(phaseApplication_resolution runtime leaks
                  (originalCoordinate owner)).respond
                  execution actor _ (encodeInputs (Env.empty (CellVal simpleExpr))) valid ordered
                    resolved, ?_⟩
                rwa [app.respond_environmentRecall]
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro owner unsent
                  have beforeUnsent : ∀ message ∈ app.outputs (execution.recall owner),
                      PhaseCount.event? message.payload ≠ some (originalCoordinate owner) := by
                    rwa [app.environmentStep_recall execution next command supported] at unsent
                  rcases ih owner beforeUnsent with request | ⟨resolved, clocks⟩
                  · by_cases retained : next.application.SeedRequest owner
                        (originalCoordinate owner)
                    · exact Or.inl retained
                    · exact Or.inr (original_request_loss_clock_word seeds (remaining + 1)
                        execution next prior owner request beforeUnsent command selected supported
                          retained)
                  · right
                    have publicAbsent : ¬ PhaseRuntimeState.requests
                        execution.application.publicView
                        owner (originalCoordinate owner) := by
                      intro requested
                      exact CommitAttemptEvent.Resolved.not_request (originalCoordinate owner)
                        execution.application resolved owner
                          ((execution.application.requests_publicView valid owner _).mp requested)
                    have notCallback : ¬ PhaseSeedScheduler.callback runtime leaks
                        (originalCoordinate owner) owner
                          ⟨execution.observeEnvironment app, command⟩ :=
                      fun callback => publicAbsent callback.2
                    refine ⟨(phaseApplication_resolution runtime leaks
                      (originalCoordinate owner)).environmentStep execution next command supported
                        (encodeInputs (Env.empty (CellVal simpleExpr))) valid ordered resolved, ?_⟩
                    rw [app.environmentStep_environmentRecall execution next command supported,
                      clockWord_snoc, ite_eq_right notCallback, List.append_nil]
                    exact clocks

private theorem original_idle_exhausted_clocks (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (resolved : (originalCoordinate owner).Resolved execution.application)
    (empty : PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
      execution = []) :
    (PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
      (execution.recall owner)).map Prod.fst =
        [0, 2, 3] := by
  have unsent := unsent_of_empty_emissions seeds remaining execution trace
    (originalCoordinate owner) owner empty
  obtain request | ⟨_resolved, clocks⟩ := original_silent_progress seeds trace owner unsent
  · exact (CommitAttemptEvent.Resolved.not_request (originalCoordinate owner)
      execution.application resolved owner request).elim
  · have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
      horizon (family seeds) remaining execution trace owner (originalCoordinate owner)
    rw [← words, word_clock_projection]
    exact clocks

/-- An original binding episode with no emitted service packet exhausts its
entire clock calendar when it resolves. The conclusion concerns the original
coordinate even after retry, phase advance, or exhausted restoration. -/
theorem original_binding_exhausted_clocks (seeds : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player)
    (resolved : (originalCoordinate owner).Resolved current.execution.application)
    (empty : PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
      current.execution = []) :
    (PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
      (current.execution.recall owner)).map Prod.fst =
        [0, 2, 3] := by
  classical
  rcases current with ⟨remaining, active, execution⟩
  cases active with
  | none =>
      exact original_idle_exhausted_clocks seeds remaining execution trace owner resolved empty
  | some actor =>
      obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seeds) remaining
        execution actor ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds actor _ _)
      have afterResolved : (originalCoordinate owner).Resolved
          (execution.respond app actor ⟨none⟩).application := resolved
      have afterEmpty : PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner)
          owner (execution.respond app actor ⟨none⟩) = [] := empty
      have valid := raw_native_valid (family seeds) _
        (countedMenu.toRawTrace initial horizon (family seeds) trace)
      have absent : ¬ PhaseRuntimeState.requests (execution.observe app owner).application.2
          owner (originalCoordinate owner) := by
        intro requested
        exact CommitAttemptEvent.Resolved.not_request (originalCoordinate owner)
          execution.application resolved owner
            ((execution.application.requests_publicView valid owner _).mp requested)
      have afterWord : PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
          ((execution.respond app actor ⟨none⟩).recall owner) =
            PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
              (execution.recall owner) := by
        by_cases same : owner = actor
        · subst actor
          simp only [ReactiveApplication.Execution.respond, ite_true,
            PhaseSeedScheduler.ownerWord, List.filter_append, List.filter_cons, List.filter_nil,
            absent, decide_false, Bool.false_eq_true, ite_false, List.append_nil]
        · rw [app.respond_recall_other execution actor owner same ⟨none⟩]
      have result := original_idle_exhausted_clocks seeds remaining
        (execution.respond app actor ⟨none⟩) responded owner afterResolved afterEmpty
      rwa [afterWord] at result

end Vegas.Examples.CommitSeedBroadcast
