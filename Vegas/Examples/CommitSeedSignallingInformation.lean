/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingService
import Vegas.Examples.CommitSeedSignallingAudit
import Vegas.Examples.CommitSeedSignallingSeedTrace
import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveMessageReadout
import Interaction.ReactiveSchedulerTranscript
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveCompleteObservation

/-! # The actual initial callbacks of the private-seed service -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- The deterministic sample of the existing complete-observation transition. -/
def completeActivation (execution : app.Execution) (owner : Player) : app.Execution :=
  execution.sampledActivation app owner (execution.network.pending.map Message.id).toFinset

theorem completeActivation_law (execution : app.Execution) (owner : Player) :
    execution.environmentStep app (.activate owner) =
      PMF.pure (completeActivation execution owner) := by
  rw [ReactiveApplication.Execution.activation_samples]
  change (MessageNetwork.completePendingObservation owner execution.network.pending).map _ = _
  simp only [MessageNetwork.completePendingObservation, PMF.pure_map, completeActivation]

def aliceFirst : app.Execution := completeActivation initialExecution alice

def aliceResponded (response : app.Action) : app.Execution :=
  aliceFirst.respond app alice response

def bobFirst (response : app.Action) : app.Execution :=
  completeActivation (aliceResponded response) bob

def aliceFirstInput : app.Info := some (aliceFirst.recall alice, aliceFirst.observe app alice)

def bobQuietInput : app.Info :=
  some ((bobFirst ⟨none⟩).recall bob, (bobFirst ⟨none⟩).observe app bob)

theorem aliceFirst_application : aliceFirst.application = initialState := rfl

theorem aliceFirst_network : aliceFirst.network = MessageNetwork.empty := by
  simp only [aliceFirst, completeActivation, initialExecution,
    ReactiveApplication.Execution.initial, ReactiveApplication.Execution.sampledActivation,
    MessageNetwork.empty, List.map_nil, List.toFinset_nil, MessageNetwork.learn_empty]

theorem aliceFirst_recall (owner : Player) : aliceFirst.recall owner = [] := rfl

theorem aliceFirst_environmentRecall : aliceFirst.environmentRecall =
    [⟨initialExecution.observeEnvironment app, .activate alice⟩] := rfl

theorem aliceResponded_environmentRecall (response : app.Action) :
    (aliceResponded response).environmentRecall = aliceFirst.environmentRecall :=
  app.respond_environmentRecall aliceFirst alice response

theorem bobFirst_environmentRecall (response : app.Action) :
    (bobFirst response).environmentRecall =
      [⟨initialExecution.observeEnvironment app, .activate alice⟩,
        ⟨(aliceResponded response).observeEnvironment app, .activate bob⟩] := by
  rw [bobFirst, completeActivation, ReactiveApplication.Execution.sampledActivation]
  rw [aliceResponded_environmentRecall, aliceFirst_environmentRecall]
  rfl

theorem bobFirst_recall (response : app.Action) : (bobFirst response).recall bob = [] := by
  change (aliceFirst.respond app alice response).recall bob = []
  rw [app.respond_recall_other _ alice bob (by decide), aliceFirst_recall]

theorem aliceResponded_quiet_application :
    (aliceResponded ⟨none⟩).application = initialState := rfl

theorem aliceResponded_quiet_network :
    (aliceResponded ⟨none⟩).network = MessageNetwork.empty := aliceFirst_network

theorem aliceResponded_public (response : app.Action) :
    (aliceResponded response).application.publicView = initialState.publicView := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      change (PhaseRuntimeState.submit initialState alice submission).publicView = _
      simp only [PhaseRuntimeState.submit, PhaseRuntimeState.publicView, RecoveryState.submit,
        submitStep_publicView, (submission.call.register_facts alice initialState.current.native).2,
        PhaseRuntimeState.attempt]

theorem aliceResponded_attempt (response : app.Action) :
    (aliceResponded response).application.attempt = originalAttempt := by
  have same := congrArg PhasePublicView.attempt (aliceResponded_public response)
  exact same.trans initialState_attempt

theorem bobFirst_quiet_application :
    (bobFirst ⟨none⟩).application = initialState := rfl

theorem bobFirst_quiet_network :
    (bobFirst ⟨none⟩).network = MessageNetwork.empty := by
  simp only [bobFirst, completeActivation, ReactiveApplication.Execution.sampledActivation,
    aliceResponded_quiet_network, MessageNetwork.empty, List.map_nil, List.toFinset_nil,
    MessageNetwork.learn_empty]

theorem bobFirst_quiet_messages :
    ((bobFirst ⟨none⟩).observe app bob).messages = ⟨[], []⟩ := by
  simp only [ReactiveApplication.Execution.observe, bobFirst_quiet_network,
    MessageNetwork.observe, MessageNetwork.empty]

/-- A raw transmission cannot be hidden from the second initial callback.
No assertion about successful submission, admissibility or its payload is needed. -/
theorem bobFirst_empty_leaks_iff (response : app.Action) :
    ((bobFirst response).observe app bob).messages.leaked = [] ↔
      response.transmission = none := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => simp only [bobFirst_quiet_messages]
  | some submission =>
      simp [bobFirst, completeActivation, aliceResponded, ReactiveApplication.Execution.respond,
        ReactiveApplication.Execution.sampledActivation, ReactiveApplication.Execution.observe,
        aliceFirst_network, MessageNetwork.submit, MessageNetwork.empty, MessageNetwork.learn,
        MessageNetwork.known, MessageNetwork.lookup, MessageNetwork.observe, Message.sender,
        OnePacketCommitRevealHypotheses.alice, OnePacketCommitRevealHypotheses.bob]

theorem bobFirst_quiet_input_iff (response : app.Action) :
    some ((bobFirst response).recall bob, (bobFirst response).observe app bob) =
        bobQuietInput ↔ response = ⟨none⟩ := by
  constructor
  · intro equal
    have same := congrArg (fun input : app.Info =>
      input.map (fun pair => pair.2.messages.leaked)) equal
    have empty : ((bobFirst response).observe app bob).messages.leaked = [] := by
      simpa only [bobQuietInput, Option.map_some, bobFirst_quiet_messages,
        Option.some.injEq] using same
    have quiet := (bobFirst_empty_leaks_iff response).mp empty
    cases response
    cases quiet
    rfl
  · rintro rfl
    rfl

theorem family_first (seeds : Seeds) :
    family seeds initialExecution.environmentRecall (initialExecution.observeEnvironment app) =
      PMF.pure (.activate alice) := by
  rw [family_apply, choose_original _ _ _ initialState_attempt]
  change PMF.pure (activateReady alice aliceBinding _) = _
  rw [activateReady, initial_bindings_ready.1]
  rfl

theorem family_after_alice (seeds : Seeds) (response : app.Action) :
    family seeds (aliceResponded response).environmentRecall
        ((aliceResponded response).observeEnvironment app) = PMF.pure (.activate bob) := by
  classical
  rw [family_apply, choose_original _ _ _ (aliceResponded_attempt response)]
  rw [aliceResponded_environmentRecall, aliceFirst_environmentRecall]
  change PMF.pure (activateReady bob bobBinding _) = _
  have ready : ready bob bobBinding ((aliceResponded response).observeEnvironment app) = true := by
    unfold ready
    change decide (PhaseRuntimeState.requests (aliceResponded response).application.publicView
      bob ⟨(aliceResponded response).application.attempt, bobBinding⟩) = true
    rw [aliceResponded_public, aliceResponded_attempt]
    have originalReady := initial_bindings_ready.2
    change decide (PhaseRuntimeState.requests initialState.publicView bob
      ⟨initialState.attempt, bobBinding⟩) = true at originalReady
    rw [initialState_attempt] at originalReady
    exact originalReady
  rw [activateReady, ready]
  rfl

theorem first_command_consistent (seeds : Seeds) :
    app.commandConsistentFrom choose seeds [] aliceFirst.environmentRecall := by
  rw [aliceFirst_environmentRecall]
  change choose seeds [] (initialExecution.observeEnvironment app) = .activate alice ∧ True
  constructor
  · have member : (.activate alice : app.Command) ∈
        (family seeds [] (initialExecution.observeEnvironment app)).support := by
      change (.activate alice : app.Command) ∈
        (family seeds initialExecution.environmentRecall
          (initialExecution.observeEnvironment app)).support
      rw [family_first]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    exact ((PMF.mem_support_pure_iff _ _).mp member).symm
  · trivial

theorem first_two_commands_consistent (seeds : Seeds) (response : app.Action) :
    app.commandConsistentFrom choose seeds [] (bobFirst response).environmentRecall := by
  rw [bobFirst_environmentRecall]
  change choose seeds [] (initialExecution.observeEnvironment app) = .activate alice ∧
    choose seeds [⟨initialExecution.observeEnvironment app, .activate alice⟩]
      ((aliceResponded response).observeEnvironment app) = .activate bob ∧ True
  refine ⟨(first_command_consistent seeds).1, ?_, trivial⟩
  have member : (.activate bob : app.Command) ∈
      (family seeds (aliceResponded response).environmentRecall
        ((aliceResponded response).observeEnvironment app)).support := by
    rw [family_after_alice]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  exact ((PMF.mem_support_pure_iff _ _).mp member).symm

theorem initial_seed_posterior : implementation.posterior [] = seedPrior := rfl

theorem aliceFirst_seed_posterior :
    implementation.posterior aliceFirst.environmentRecall = seedPrior := by
  obtain ⟨seed, supported⟩ := seedPrior.support_nonempty
  have positive : ∃ seed ∈ {seed | app.commandConsistentFrom choose seed []
      aliceFirst.environmentRecall}, seed ∈ seedPrior.support :=
    ⟨seed, first_command_consistent seed, supported⟩
  change (app.schedulerMixture seedPrior (fun seed past view =>
    PMF.pure (choose seed past view))).posterior aliceFirst.environmentRecall = seedPrior
  rw [app.schedulerMixture_posterior_eq_filter seedPrior choose _ positive]
  exact filter_of_support_subset _ _ _ (fun seed _ => first_command_consistent seed)

theorem bobFirst_seed_posterior (response : app.Action) :
    implementation.posterior (bobFirst response).environmentRecall = seedPrior := by
  obtain ⟨seed, supported⟩ := seedPrior.support_nonempty
  have positive : ∃ seed ∈ {seed | app.commandConsistentFrom choose seed []
      (bobFirst response).environmentRecall}, seed ∈ seedPrior.support :=
    ⟨seed, first_two_commands_consistent seed response, supported⟩
  change (app.schedulerMixture seedPrior (fun seed past view =>
    PMF.pure (choose seed past view))).posterior (bobFirst response).environmentRecall = seedPrior
  rw [app.schedulerMixture_posterior_eq_filter seedPrior choose _ positive]
  exact filter_of_support_subset _ _ _ (fun seed _ => first_two_commands_consistent seed response)

theorem scheduler_first :
    scheduler initialExecution.environmentRecall (initialExecution.observeEnvironment app) =
      PMF.pure (.activate alice) := by
  change implementation.scheduler _ _ = _
  rw [ReactiveApplication.SchedulerImplementation.scheduler_eq]
  simp only [implementation,
    ReactiveApplication.schedulerMixture, family_first, PMF.pure_map, PMF.map_bind,
    PMF.bind_const]

theorem scheduler_after_alice (response : app.Action) :
    scheduler (aliceResponded response).environmentRecall
        ((aliceResponded response).observeEnvironment app) = PMF.pure (.activate bob) := by
  change implementation.scheduler _ _ = _
  rw [ReactiveApplication.SchedulerImplementation.scheduler_eq,
    aliceResponded_environmentRecall, aliceFirst_seed_posterior]
  change (seedPrior.bind fun seed =>
    (family seed (aliceResponded response).environmentRecall
      ((aliceResponded response).observeEnvironment app)).map
        fun command => (command, seed)).map Prod.fst = _
  simp only [family_after_alice, PMF.pure_map, PMF.map_bind,
    PMF.bind_const]

private theorem raw_silent_available (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) : (⟨none⟩ : app.Action) ∈ rawMenu.actions owner past view := by
  classical
  change (⟨none⟩ : app.Action) ∈ insert _ _
  exact Finset.mem_insert_self _ _

theorem aliceFirst_trace : Nonempty (rawProtocol.Trace
    (some ⟨63, some alice, aliceFirst⟩)) := by
  obtain ⟨initialTrace⟩ := rawMenu.trace_initial initial horizon scheduler initialState
    (by rw [initial_eq_pure]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  apply rawMenu.trace_environment initial horizon scheduler 63 initialExecution aliceFirst
    (.activate alice) initialTrace
  · rw [scheduler_first]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

theorem bobFirst_quiet_trace : Nonempty (rawProtocol.Trace
    (some ⟨62, some bob, bobFirst ⟨none⟩⟩)) := by
  obtain ⟨first⟩ := aliceFirst_trace
  obtain ⟨responded⟩ := rawMenu.trace_respond initial horizon scheduler 63 aliceFirst alice
    ⟨none⟩ first (raw_silent_available alice _ _)
  apply rawMenu.trace_environment initial horizon scheduler 62 (aliceResponded ⟨none⟩)
    (bobFirst ⟨none⟩) (.activate bob) responded
  · rw [scheduler_after_alice]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · rw [completeActivation_law]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

def aliceFirstHistory : rawProtocol.History := ⟨_, aliceFirst_trace.some⟩

def bobQuietHistory : rawProtocol.History := ⟨_, bobFirst_quiet_trace.some⟩

theorem aliceFirstHistory_info :
    rawModel.infoOf alice aliceFirstHistory.trace = aliceFirstInput := by
  change (rawMenu.signals initial horizon scheduler).infoOf alice aliceFirstHistory.trace = _
  rw [rawMenu.info]
  rfl

theorem bobQuietHistory_info :
    rawModel.infoOf bob bobQuietHistory.trace = bobQuietInput := by
  change (rawMenu.signals initial horizon scheduler).infoOf bob bobQuietHistory.trace = _
  rw [rawMenu.info]
  rfl

def aliceFirstSite : rawModel.InformationSite alice := by
  refine ⟨aliceFirstInput, ⟨⟨aliceFirstHistory, aliceFirstHistory_info⟩, ?_, ⟨⟨none⟩, ?_⟩⟩⟩
  · intro stopped
    exact (by decide : (some alice : Option Player) ≠ none) stopped.2
  · exact ⟨⟨none⟩, raw_silent_available alice _ _, rfl⟩

def bobQuietSite : rawModel.InformationSite bob := by
  refine ⟨bobQuietInput, ⟨⟨bobQuietHistory, bobQuietHistory_info⟩, ?_, ⟨⟨none⟩, ?_⟩⟩⟩
  · intro stopped
    exact (by decide : (some bob : Option Player) ≠ none) stopped.2
  · exact ⟨⟨none⟩, raw_silent_available bob _ _, rfl⟩

/-- This is the actual first scheduler round, with an arbitrary raw Alice law. -/
theorem first_round (players : Player → app.Policy) (seeds : Seeds) :
    app.round (family seeds) players initialExecution =
      (players alice [] (aliceFirst.observe app alice)).map aliceResponded := by
  rw [ReactiveApplication.round, family_first, PMF.pure_bind]
  rw [ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
  rfl

theorem first_round_integrated (players : Player → app.Policy) :
    app.round scheduler players initialExecution =
      (players alice [] (aliceFirst.observe app alice)).map aliceResponded := by
  rw [ReactiveApplication.round, scheduler_first, PMF.pure_bind]
  rw [ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind]
  rfl

/-- The second activation occurs for every first raw response, before Bob
responds and before any seed-dependent scheduler command. -/
theorem bobFirst_command_law (players : Player → app.Policy) (seeds : Seeds) :
    (app.runRounds (family seeds) players 1 initialExecution).bind (fun execution =>
      (family seeds execution.environmentRecall (execution.observeEnvironment app)).bind
        fun command => (execution.environmentStep app command).map
          fun next => (command, next)) =
      (players alice [] (aliceFirst.observe app alice)).map
        fun response => (.activate bob, bobFirst response) := by
  simp only [ReactiveApplication.runRounds, first_round, PMF.bind_map, Function.comp_def,
    PMF.pure_bind, PMF.bind_pure, family_after_alice, completeActivation_law, PMF.pure_map]
  rfl

/-- Every legal mixed-scheduler decision is also a genuine fixed-original-seed
decision. This uses the actual posterior and the existing round evaluator. -/
theorem fixed_seed_decision (current : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some current)) :
    ∃ seed, Nonempty ((app.protocol initial horizon (family seed)).Trace (some current)) := by
  obtain ⟨seed, _supported, fixed⟩ := raw_trace_fixed_seed current trace
  exact ⟨seed, fixed⟩

theorem original_zero_clock_index_mixed (current : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (zero : current.execution.application.current.native.clock = 0) :
    current.execution.environmentRecall.length ≤ 2 := by
  obtain ⟨seed, ⟨fixed⟩⟩ := fixed_seed_decision current trace
  exact original_zero_clock_index seed current fixed original zero

/-- The two zero-clock original decision states are completely determined by
the actual first raw response; no private seed appears in this classification. -/
theorem original_zero_clock_decision (current : app.Control) (owner : Player)
    (trace : (app.protocol initial horizon scheduler).Trace (some current))
    (active : current.actor = some owner)
    (original : current.execution.application.attempt = originalAttempt)
    (zero : current.execution.application.current.native.clock = 0) :
    (owner = alice ∧ current = ⟨63, some alice, aliceFirst⟩) ∨
      (owner = bob ∧ ∃ response, current = ⟨62, some bob, bobFirst response⟩) := by
  have small := original_zero_clock_index_mixed current trace original zero
  have accounted := app.raw_trace_horizon initial horizon scheduler trace
  change current.execution.environmentRecall.length + current.remaining = 64 at accounted
  let fallback : Player → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy current.execution fallback
  have actual := ReactiveApplication.anchored_of_trace initial horizon scheduler current.execution
    fallback trace current rfl (fun _ => List.prefix_refl _)
  rw [active] at actual
  obtain ⟨_bounded, strict, before, reached, command, selected, actor, observed⟩ := actual
  have positions : horizon - current.remaining - 1 = 0 ∨
      horizon - current.remaining - 1 = 1 := by
    change current.remaining < 64 at strict
    change 64 - current.remaining - 1 = 0 ∨ 64 - current.remaining - 1 = 1
    omega
  rcases positions with position | position
  all_goals rw [position] at reached
  · have beforeEq : before = initialExecution := by
      simpa only [ReactiveApplication.roundsFrom, ReactiveApplication.runRounds,
        initial_eq_pure, PMF.pure_bind, PMF.mem_support_pure_iff, initialExecution] using reached
    subst before
    rw [scheduler_first, PMF.mem_support_pure_iff] at selected
    subst command
    have sameOwner : owner = alice := (Option.some.inj actor).symm
    have sameExecution : current.execution = aliceFirst := by
      simpa only [completeActivation_law, PMF.mem_support_pure_iff, aliceFirst] using observed
    left
    refine ⟨sameOwner, ?_⟩
    have remaining : current.remaining = 63 := by
      change current.remaining < 64 at strict
      change 64 - current.remaining - 1 = 0 at position
      omega
    cases current
    simp_all
  · have first : app.roundsFrom initial scheduler players 1 =
        (players alice [] (aliceFirst.observe app alice)).map
          aliceResponded := by
      rw [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind]
      change app.runRounds scheduler players 1 initialExecution = _
      rw [ReactiveApplication.runRounds]
      change (app.round scheduler players initialExecution).bind PMF.pure = _
      rw [PMF.bind_pure]
      exact first_round_integrated players
    rw [first, PMF.support_map] at reached
    obtain ⟨response, _, same⟩ := reached
    subst before
    rw [scheduler_after_alice, PMF.mem_support_pure_iff] at selected
    subst command
    have sameOwner : owner = bob := (Option.some.inj actor).symm
    have sameExecution : current.execution = bobFirst response := by
      simpa only [completeActivation_law, PMF.mem_support_pure_iff, bobFirst] using observed
    right
    refine ⟨sameOwner, response, ?_⟩
    have remaining : current.remaining = 62 := by
      change current.remaining < 64 at strict
      change 64 - current.remaining - 1 = 1 at position
      omega
    cases current
    simp_all

theorem aliceFirst_information_state
    (history : rawModel.InformationHistory alice aliceFirstSite.1) :
    history.1.state = some ⟨63, some alice, aliceFirst⟩ := by
  have observed := (rawMenu.info initial horizon scheduler alice history.1.trace).symm.trans
    history.2
  change app.observe alice history.1.state = aliceFirstInput at observed
  cases state : history.1.state with
  | none => simp only [state, ReactiveApplication.observe] at observed; cases observed
  | some current =>
      by_cases active : current.actor = some alice
      · simp only [state, ReactiveApplication.observe, active, ↓reduceIte,
          aliceFirstInput, Option.some.injEq] at observed
        have view := (Prod.mk.inj observed).2
        have original : current.execution.application.attempt = originalAttempt := by
          have same := congrArg (fun view : app.PlayerView => view.application.2.attempt) view
          exact same.trans initialState_attempt
        have zero : current.execution.application.current.native.clock = 0 := by
          have same := congrArg (fun view : app.PlayerView => view.application.2.native.clock) view
          exact same.trans initialState_clock
        obtain (⟨_, currentEq⟩ | ⟨impossible, _⟩) :=
          original_zero_clock_decision current alice
            (rawMenu.toRawTrace initial horizon scheduler (state ▸ history.1.trace))
              active original zero
        · exact congrArg some currentEq
        · cases (by decide : alice ≠ bob) impossible
      · simp only [state, ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

theorem bobQuiet_information_state
    (history : rawModel.InformationHistory bob bobQuietSite.1) :
    history.1.state = some ⟨62, some bob, bobFirst ⟨none⟩⟩ := by
  have observed := (rawMenu.info initial horizon scheduler bob history.1.trace).symm.trans
    history.2
  change app.observe bob history.1.state = bobQuietInput at observed
  cases state : history.1.state with
  | none => simp only [state, ReactiveApplication.observe] at observed; cases observed
  | some current =>
      by_cases active : current.actor = some bob
      · simp only [state, ReactiveApplication.observe, active, ↓reduceIte,
          bobQuietInput, Option.some.injEq] at observed
        have view := (Prod.mk.inj observed).2
        have original : current.execution.application.attempt = originalAttempt := by
          have same := congrArg (fun view : app.PlayerView => view.application.2.attempt) view
          exact same.trans initialState_attempt
        have zero : current.execution.application.current.native.clock = 0 := by
          have same := congrArg (fun view : app.PlayerView => view.application.2.native.clock) view
          exact same.trans initialState_clock
        obtain (⟨impossible, _⟩ | ⟨_, response, currentEq⟩) :=
          original_zero_clock_decision current bob
            (rawMenu.toRawTrace initial horizon scheduler (state ▸ history.1.trace))
              active original zero
        · cases (by decide : bob ≠ alice) impossible
        · have quiet : response = ⟨none⟩ := by
            apply (bobFirst_quiet_input_iff response).mp
            simpa only [currentEq, bobQuietInput] using congrArg some observed
          exact congrArg some (quiet ▸ currentEq)
      · simp only [state, ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

end Vegas.Examples.CommitSeedSignalling
