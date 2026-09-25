/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeChronology
import VegasTests.MonitoredGuessingNativeMonitoring
import Vegas.Pending.EventOpponentFrame
import VegasTests.MonitoredGuessingNativeInitial

/-! # Alice's publication cannot settle before her service visit -/

noncomputable section
namespace VegasTests.MonitoredGuessing
open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem native_player_step (players : Player → nativeApp.Policy) (who : Player)
    (execution : nativeApp.Execution) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork (.player who) execution =
      (execution.environmentStep nativeApp (.activate who)).bind (nativeApp.invoke players who) :=
    by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch]
  rfl

theorem prelude_report_config (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) (reply : nativeApp.Action) :
    (reported (watcherRespond bit action selected reply)).application.config =
      (nativeInitial bit).config := by
  unfold reported
  cases reportCommand (watcherRespond bit action selected reply) with
  | «include» id => exact prelude_include_config bit action selected reply id
  | activate who | application command | wait => exact watcher_config bit action selected reply

theorem native_prelude_config (bit : Bool) (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.player alice, .player watcher, .wire] (nativeStart bit)).support) :
    execution.application.config = (nativeInitial bit).config := by
  simp only [runInteractionPlan, FinDist.bind_pure, report_step, native_player_step,
    initial_activation, FinDist.pure_bind, ReactiveApplication.invoke,
    FinDist.bind_map, FinDist.bind_bind] at reached
  obtain ⟨action, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  change execution ∈ ((ambientRespond bit action).environmentStep nativeApp (.activate watcher)
    |>.bind fun observed =>
      (players watcher (observed.recall watcher) (observed.observe nativeApp watcher)).bind
        fun reply => FinDist.pure (reported
          (observed.respond nativeApp watcher reply))).support at reached
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.bind_map] at reached
  obtain ⟨selected, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨reply, _, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  change execution ∈ (FinDist.pure
    (reported (watcherRespond bit action selected reply))).support at reached
  rw [FinDist.mem_support_pure] at reached
  subst execution
  exact prelude_report_config bit action selected reply

theorem foreign_handle_keeps_alice_unfinished (before after : State nativeGraph)
    (message : Message Player (Payload nativeGraph)) (foreign : message.sender ≠ alice)
    (accepted : handle nativeRuntime before message = some after)
    (unfinished : alicePublication ∉ before.config.cut.completed) :
    alicePublication ∉ after.config.cut.completed := by
  exact fun completed => unfinished ((handle_opponent_completed_iff nativeRuntime before after
    message alicePublication alice rfl (Ne.symm foreign) accepted).mp completed)

theorem bob_include_keeps_alice_unfinished (execution : nativeApp.Execution)
    (id : MessageId Player) (owner : id.1 = bob)
    (unfinished : alicePublication ∉ execution.application.config.cut.completed) :
    alicePublication ∉ (execution.includePending nativeApp id).application.config.cut.completed :=
    by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => exact unfinished
  | some message =>
      have same : message.id = id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have foreign : message.sender ≠ alice := by
        change message.id.1 ≠ alice
        rw [same, owner]
        decide
      change alicePublication ∉
        ((handle nativeRuntime execution.application ⟨message.id, message.payload.call⟩).getD
          execution.application).config.cut.completed
      cases accepted : handle nativeRuntime execution.application
          ⟨message.id, message.payload.call⟩ with
      | none => exact unfinished
      | some after =>
          exact foreign_handle_keeps_alice_unfinished execution.application after
            ⟨message.id, message.payload.call⟩ foreign accepted unfinished

theorem native_player_keeps_alice_unfinished (players : Player → nativeApp.Policy)
    (who : Player) (before after : nativeApp.Execution)
    (unfinished : alicePublication ∉ before.application.config.cut.completed)
    (reached : after ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.player who) before).support) :
    alicePublication ∉ after.application.config.cut.completed := by
  rw [native_player_step] at reached
  obtain ⟨observed, activated, responded⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ responded
  rw [(nativeRuntime.reactive_respond_application nativeLeaks observed who action).1]
  obtain ⟨next, support, same⟩ := FinDist.support_map .. ▸ activated
  rw [← same]
  obtain ⟨selected, _, sameNext⟩ := FinDist.support_map .. ▸ support
  rw [← sameNext]
  exact unfinished

theorem native_bob_include_unfinished (players : Player → nativeApp.Policy)
    (before after : nativeApp.Execution)
    (unfinished : alicePublication ∉ before.application.config.cut.completed)
    (reached : after ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob) before).support) :
    alicePublication ∉ after.application.config.cut.completed := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind] at reached
  rcases nativeRuntime.reactiveLatest_wait_or_owned nativeLeaks bobPublication bob
      (before.observeEnvironment nativeApp) with silent | ⟨id, owner, selected⟩
  · rw [silent] at reached
    change after ∈ (before.environmentStep nativeApp .wait |>.bind FinDist.pure).support at reached
    rw [FinDist.bind_pure] at reached
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at reached
    subst after
    exact unfinished
  · rw [selected] at reached
    change after ∈ ((before.environmentStep nativeApp (.include id)).bind
      FinDist.pure).support at reached
    rw [FinDist.bind_pure] at reached
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at reached
    subst after
    exact bob_include_keeps_alice_unfinished before id owner unfinished

theorem native_maintenance_unfinished (players : Player → nativeApp.Policy)
    (before after : nativeApp.Execution) (instruction : ServiceInstruction nativeGraph)
    (allowed : instruction = .grant bobPublication ∨ instruction = .grant alicePublication ∨
      instruction = .tick ∨ instruction = .expire bobPublication)
    (unfinished : alicePublication ∉ before.application.config.cut.completed)
    (reached : after ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      instruction before).support) : alicePublication ∉ after.application.config.cut.completed :=
    by
  rcases allowed with rfl | rfl | rfl | rfl
  all_goals
    have moved := nativeRuntime.reactive_application_support nativeLeaks players _ before after
      (by simpa only [interactionStep, interactionInstruction, FinDist.pure_bind] using reached)
  · rw [FinDist.mem_support_pure.mp moved]
    exact unfinished
  · rw [FinDist.mem_support_pure.mp moved]
    exact unfinished
  · rw [FinDist.mem_support_pure.mp moved]
    exact unfinished
  · rcases nativeRuntime.environmentStep_expire_config_eq_or_mem_step
      before.application after.application bobPublication moved with same | ⟨ready, action, step⟩
    · rwa [same]
    · rw [before.application.config.step_cut bobPublication ready action after.application.config
        step, EventOrder.Cut.mem_complete]
      simpa only [show alicePublication ≠ bobPublication by decide, false_or] using unfinished

theorem native_bob_visit_unfinished (players : Player → nativeApp.Policy)
    (before after : nativeApp.Execution)
    (unfinished : alicePublication ∉ before.application.config.cut.completed)
    (reached : after ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeVisit bobPublication) before).support) :
    alicePublication ∉ after.application.config.cut.completed := by
  have preserve : ∀ instruction ∈ nativeVisit bobPublication, ∀ before after : nativeApp.Execution,
      alicePublication ∉ before.application.config.cut.completed →
      after ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        instruction before).support → alicePublication ∉ after.application.config.cut.completed :=
      by
    intro instruction member previous next prior moved
    have cases : instruction = .grant bobPublication ∨ instruction = .player bob ∨
        instruction = .includeLatest bobPublication bob ∨ instruction = .tick ∨
          instruction = .expire bobPublication := by
      simpa only [nativeVisit, nativeOwner, ite_true, nativeRuntime, bobPublication,
        pow_zero, List.replicate_one, List.mem_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false, or_assoc] using member
    rcases cases with rfl | rfl | rfl | rfl | rfl
    · exact native_maintenance_unfinished players previous next _ (Or.inl rfl) prior moved
    · exact native_player_keeps_alice_unfinished players bob previous next prior moved
    · exact native_bob_include_unfinished players previous next prior moved
    · exact native_maintenance_unfinished players previous next _
        (Or.inr (Or.inr (Or.inl rfl))) prior moved
    · exact native_maintenance_unfinished players previous next _
        (Or.inr (Or.inr (Or.inr rfl))) prior moved
  generalize planEq : nativeVisit bobPublication = plan at reached
  have all : ∀ instruction ∈ plan, ∀ before after : nativeApp.Execution,
      alicePublication ∉ before.application.config.cut.completed →
      after ∈ (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        instruction before).support → alicePublication ∉ after.application.config.cut.completed :=
    by simpa only [← planEq] using preserve
  clear preserve planEq
  induction plan generalizing before with
  | nil => cases FinDist.mem_support_pure.mp reached; exact unfinished
  | cons instruction rest ih =>
      obtain ⟨middle, first, restMem⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      exact ih middle (all instruction (List.mem_cons_self) before middle unfinished first)
        restMem (fun next member => all next (List.mem_cons_of_mem instruction member))

theorem native_before_alice_unfinished (bit : Bool) (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeBefore 1) (nativeStart bit)).support) :
    alicePublication ∉ execution.application.config.cut.completed := by
  rw [nativeBefore_succ bobPublication, runInteractionPlan_append] at reached
  obtain ⟨previous, prelude, later⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  apply native_bob_visit_unfinished players previous execution _ later
  rw [native_prelude_config bit players previous prelude]
  exact Finset.notMem_empty _

theorem native_rounds_prefix_support (players : Player → nativeApp.Policy)
    (count : Nat) (bounded : count ≤ nativePlan.length) (execution : nativeApp.Execution)
    (supported : execution ∈ (nativeApp.roundsFrom nativeInitialLaw nativeScheduler
      players count).support) :
    ∃ bit, execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativePlan.take count) (nativeStart bit)).support := by
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ stateMem
  refine ⟨bit, ?_⟩
  have law := native_segment_rounds players [] (nativePlan.take count) (nativePlan.drop count)
    (by simp) (nativeStart bit) rfl
  rw [List.length_take_of_le bounded] at law
  change execution ∈ (nativeApp.runRounds nativeScheduler players count (nativeStart bit)).support
    at reached
  rwa [law] at reached

theorem native_grant_application (players : Player → nativeApp.Policy)
    (event : nativeGraph.EventId) (before after : nativeApp.Execution)
    (supported : after ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.grant event] before).support) :
    after.application = { before.application with serviceGrant := some event } := by
  have moved := nativeRuntime.reactive_application_support nativeLeaks players (.grant event)
    before after (by
      simpa only [runInteractionPlan, FinDist.bind_pure, interactionStep, interactionInstruction,
        FinDist.pure_bind] using supported)
  exact FinDist.mem_support_pure.mp moved

theorem native_activation_application (before after : nativeApp.Execution) (who : Player)
    (supported : after ∈ (before.environmentStep nativeApp (.activate who)).support) :
    after.application = before.application := by
  obtain ⟨next, member, same⟩ := FinDist.support_map .. ▸ supported
  rw [← same]
  obtain ⟨selected, _, sameNext⟩ := FinDist.support_map .. ▸ member
  rw [← sameNext]

theorem native_alice_final_calendar (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (granted : control.execution.application.serviceGrant = some alicePublication) :
    control.execution.environmentRecall.length = 10 ∧ control.remaining = 4 := by
  rcases native_alice_calendar control trace active with early | late
  · obtain ⟨bit, same⟩ := native_alice_initial_representation control trace active early.1
    subst control
    cases granted
  · exact late

/-- Every off-path final Alice information history has a settled Bob result,
an unfinished ready publication, and enough time for its reserved inclusion. -/
theorem native_alice_final_service (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (granted : control.execution.application.serviceGrant = some alicePublication) :
    bobPublication ∈ control.execution.application.config.cut.completed ∧
      control.execution.application.config.cut.Ready alicePublication ∧
      control.execution.application.WithinDeadline nativeRuntime alicePublication := by
  have calendar := native_alice_final_calendar control trace active granted
  obtain ⟨_, supported⟩ := nativeMenu.roundSupported_uniform nativeInitialLaw
    nativeHorizon nativeScheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, _, actor, observed⟩ := supported
  have counted : count = 9 := by omega
  subst count
  obtain ⟨bit, prefixMem⟩ := native_rounds_prefix_support nativeMenu.uniformResponses 9
    (by decide) prior priorMem
  rw [show nativePlan.take 9 = nativeBefore 1 ++ [.grant alicePublication] from rfl,
    runInteractionPlan_append] at prefixMem
  obtain ⟨previous, beforeMem, grantMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ prefixMem)
  have unfinished := native_before_alice_unfinished bit nativeMenu.uniformResponses previous
    beforeMem
  have ready := (native_before_available bit nativeMenu.uniformResponses alicePublication previous
    beforeMem).resolve_left unfinished
  have timely := native_before_timely bit nativeMenu.uniformResponses alicePublication previous
    beforeMem unfinished
  have bobDone := native_before_completed bit nativeMenu.uniformResponses 1 (by decide) previous
    beforeMem bobPublication (by decide)
  have grantApp := native_grant_application nativeMenu.uniformResponses alicePublication
    previous prior grantMem
  have commandEq : command = .activate alice := by
    cases command with
    | activate who => cases Option.some.inj actor; rfl
    | «include» id | application command | wait => cases actor
  subst command
  have observationApp := native_activation_application prior control.execution alice observed
  rw [observationApp, grantApp]
  exact ⟨bobDone, ready, timely⟩

end VegasTests.MonitoredGuessing
