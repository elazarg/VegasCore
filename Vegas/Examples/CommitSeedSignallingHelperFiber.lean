/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperInformation
import Vegas.Examples.CommitSeedSignallingPublicationWaitFiber
import Interaction.ReactiveSchedulerSeedSupport

/-! # Helper knowledge on the entire original native information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Every original posterior seed realizes the same complete physical raw
control with the same finite response menu, at idle and active boundaries. -/
theorem raw_original_posterior_trace (current : app.Control)
    (trace : rawProtocol.Trace (some current))
    (seed : Seeds)
    (supported : seed ∈ (implementation.posterior current.execution.environmentRecall).support) :
    seed ∈ seedPrior.support ∧
      Nonempty ((rawMenu.protocol initial horizon (family seed)).Trace (some current)) := by
  obtain ⟨accounted, reached⟩ := rawMenu.roundSupported_uniform initial horizon scheduler trace
  cases active : current.actor with
  | none =>
      rw [active] at reached
      have initialized : current.execution ∈ (app.runRounds scheduler rawMenu.uniformResponses
          current.execution.environmentRecall.length initialExecution).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using reached
      obtain ⟨originalSupport, originalReached⟩ :=
        app.schedulerMixture_run_of_posterior_support seedPrior family rawMenu.uniformResponses
          current.execution.environmentRecall.length initialState current.execution seed
            initialized supported
      have rounds : current.execution ∈ (app.roundsFrom initial (family seed)
          rawMenu.uniformResponses current.execution.environmentRecall.length).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using originalReached
      obtain ⟨fixed⟩ := rawMenu.trace_roundsFrom initial horizon (family seed)
        rawMenu.uniformResponses (fun who past view action member =>
          (rawMenu.uniformResponses_support who past view action).mp member)
        current.execution.environmentRecall.length (by omega) current.execution rounds
      have distance : horizon - current.execution.environmentRecall.length =
          current.remaining := by omega
      rw [distance] at fixed
      have shape : current = (⟨current.remaining, none, current.execution⟩ : app.Control) := by
        cases current with
        | mk remaining acting execution =>
            change acting = none at active
            cases active
            rfl
      rw [← shape] at fixed
      exact ⟨originalSupport, ⟨fixed⟩⟩
  | some owner =>
      rw [active] at reached
      obtain ⟨count, before, command, position, beforeReached, selected, actor, moved⟩ := reached
      have initialized : before ∈ (app.runRounds scheduler rawMenu.uniformResponses count
          initialExecution).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using beforeReached
      obtain ⟨originalSupport, original, originalReached, originalSelected, originalMoved⟩ :=
        app.schedulerMixture_decision_of_posterior_support seedPrior family rawMenu.uniformResponses
          count initialState before current.execution command seed initialized selected moved
            supported
      have rounds : original ∈ (app.roundsFrom initial (family seed) rawMenu.uniformResponses
          count).support := by
        simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
          initialExecution] using originalReached
      obtain ⟨beforeTrace⟩ := rawMenu.trace_roundsFrom initial horizon (family seed)
        rawMenu.uniformResponses (fun who past view action member =>
          (rawMenu.uniformResponses_support who past view action).mp member)
        count (by omega) original rounds
      have distance : horizon - count = current.remaining + 1 := by omega
      rw [distance] at beforeTrace
      obtain ⟨fixed⟩ := rawMenu.trace_environment initial horizon (family seed) current.remaining
        original current.execution command beforeTrace originalSelected originalMoved
      rw [actor] at fixed
      have shape : current =
          (⟨current.remaining, some owner, current.execution⟩ : app.Control) := by
        cases current with
        | mk remaining acting execution =>
            change acting = some owner at active
            cases active
            rfl
      rw [← shape] at fixed
      exact ⟨originalSupport, ⟨fixed⟩⟩

private theorem helper_request_on_same_input
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (target : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace))
    (count : Nat) (next : app.Execution)
    (state : target.1.state = some ⟨count, some alice, next⟩)
    (observed : next.observe app alice = execution.observe app alice) :
    next.application.SeedRequest alice (originalCoordinate alice) := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩) :=
    current ▸ source.trace
  have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
  have sourceValid := raw_native_valid scheduler ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
  have targetValid := raw_native_valid scheduler ⟨count, some alice, next⟩
    (rawMenu.toRawTrace initial horizon scheduler targetTrace)
  have publicRequest := (execution.application.requests_publicView sourceValid alice
    (originalCoordinate alice)).mpr request
  have publicHere : PhaseRuntimeState.requests next.application.publicView alice
      (originalCoordinate alice) := by
    change PhaseRuntimeState.requests (next.observe app alice).application.2 alice _
    rw [observed]
    exact publicRequest
  exact (next.application.requests_publicView targetValid alice (originalCoordinate alice)).mp
    publicHere

/-- Every original seed in the physical posterior at every compatible raw
history has the bit read by the actual helper observation. Histories need not
have positive probability under the assessed player profile. -/
theorem raw_helper_clock_two_information_fiber
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = bob) (addressed : message.payload.attempt = originalAttempt)
    (visible : message ∈ (execution.observe app alice).messages.leaked ∨
      message ∈ (execution.observe app alice).messages.ledger)
    (target : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace)) :
    ∃ count next, target.1.state = some (⟨count, some alice, next⟩ : app.Control) ∧
      next.recall alice = execution.recall alice ∧
      next.observe app alice = execution.observe app alice ∧
      ∀ seed ∈ (implementation.posterior next.environmentRecall).support,
        seed ∈ seedPrior.support ∧
          (seedBits seed alice = true ↔
            ∃ accepted, (message.id, accepted) ∈ (execution.observe app alice).receipts) := by
  obtain ⟨count, next, state, recalled, observed⟩ :=
    raw_information_control_of_counted_view source remaining execution alice current target
  have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
  have requested := helper_request_on_same_input source remaining execution current request
    target count next state observed
  have clockHere : next.application.current.native.clock = 2 := by
    have same := congrArg (fun view : app.PlayerView => view.application.2.native.clock) observed
    exact same.trans clock
  refine ⟨count, next, state, recalled, observed, ?_⟩
  intro seed supported
  obtain ⟨originalSupport, ⟨fixed⟩⟩ := raw_original_posterior_trace
    ⟨count, some alice, next⟩ targetTrace seed supported
  have read := alice_helper_clock_two_seed seed ⟨count, some alice, next⟩ fixed rfl requested
    clockHere message sender addressed (observed.symm ▸ visible)
  exact ⟨originalSupport, by simpa only [observed] using read⟩

/-- The complete remembered clock-two input, including its WAIT or SEND
choice, fixes the same original seed bit throughout the later raw information
fiber. A wrong-slot SEND history is not identified with an after-WAIT history. -/
theorem raw_recalled_helper_information_fiber
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (current : source.state = some ⟨remaining, some alice, execution⟩)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (message : Message Player (CommitAttemptPacket graph))
    (sender : message.sender = bob) (addressed : message.payload.attempt = originalAttempt)
    (visible : message ∈ entry.beforeView.messages.leaked ∨
      message ∈ entry.beforeView.messages.ledger)
    (target : rawModel.InformationHistory alice (countedModel.infoOf alice source.trace)) :
    ∃ count next, target.1.state = some (⟨count, some alice, next⟩ : app.Control) ∧
      next.recall alice = execution.recall alice ∧
      next.observe app alice = execution.observe app alice ∧
      ∀ seed ∈ (implementation.posterior next.environmentRecall).support,
        seed ∈ seedPrior.support ∧
          (seedBits seed alice = true ↔
            ∃ accepted, (message.id, accepted) ∈ entry.beforeView.receipts) := by
  obtain ⟨count, next, state, recalled, observed⟩ :=
    raw_information_control_of_counted_view source remaining execution alice current target
  have targetTrace : rawProtocol.Trace (some ⟨count, some alice, next⟩) := state ▸ target.1.trace
  have requested := helper_request_on_same_input source remaining execution current request
    target count next state observed
  refine ⟨count, next, state, recalled, observed, ?_⟩
  intro seed supported
  obtain ⟨originalSupport, ⟨fixed⟩⟩ := raw_original_posterior_trace
    ⟨count, some alice, next⟩ targetTrace seed supported
  have read := alice_recalled_helper_seed seed ⟨count, some alice, next⟩ fixed requested entry
    (recalled.symm ▸ recorded) clock message sender addressed visible
  exact ⟨originalSupport, read⟩

end Vegas.Examples.CommitSeedSignalling
