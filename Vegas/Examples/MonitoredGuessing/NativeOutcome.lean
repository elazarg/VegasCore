/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeResponses
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveResponseEvaluation
import Interaction.ReactiveResponseKernel
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Initialized prescribed execution of the monitored guessing game

The quiet receiver observation is realized by an actual legal history of the
bounded native runtime, including its initial draw and ordinary passive reads.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def quietAfterWire (bit : Bool) : nativeApp.Execution :=
  let previous := watcherRespond bit nativeSilent ∅ nativeSilent
  { previous with environmentRecall := previous.environmentRecall ++
    [⟨previous.observeEnvironment nativeApp, .wait⟩] }

def quietGranted (bit : Bool) : nativeApp.Execution :=
  let previous := quietAfterWire bit
  { previous with
    application := { previous.application with serviceGrant := some bobPublication }
    environmentRecall := previous.environmentRecall ++
      [⟨previous.observeEnvironment nativeApp, .application (.grant bobPublication)⟩] }

theorem quiet_watcher_activation (bit : Bool) :
    (ambientRespond bit nativeSilent).environmentStep nativeApp (.activate watcher) =
      PMF.pure (watcherActivated bit nativeSilent ∅) := by
  have pending : (ambientRespond bit nativeSilent).network.pending = [] := rfl
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    nativeLeaks, ↓reduceIte, pending, pendingIds, List.map_nil, List.toFinset_nil,
    mix_self, PMF.pure_map, MessageNetwork.learn_empty]
  simp only [watcherActivated, MessageNetwork.learn_empty]
  rfl

theorem quiet_wire (bit : Bool) :
    (watcherRespond bit nativeSilent ∅ nativeSilent).environmentStep nativeApp .wait =
      PMF.pure (quietAfterWire bit) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

theorem quiet_grant (bit : Bool) :
    (quietAfterWire bit).environmentStep nativeApp (.application (.grant bobPublication)) =
      PMF.pure (quietGranted bit) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, PMF.pure_map]
  rfl

theorem quiet_bob_activation (bit : Bool) :
    (quietGranted bit).environmentStep nativeApp (.activate bob) =
      PMF.pure (quietBob bit) := by
  have pending : (quietGranted bit).network.pending = [] := rfl
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    nativeLeaks, bob, watcher, show (1 : Player) ≠ 2 by decide, ↓reduceIte, pending,
    pendingIds, List.map_nil, List.toFinset_nil, PMF.pure_map, MessageNetwork.learn_empty]
  rfl

theorem quiet_ambient_trace (bit : Bool) :
    Nonempty (nativeArena.Trace (some ⟨13, none, ambientRespond bit nativeSilent⟩)) := by
  obtain ⟨initial⟩ := native_initial_trace bit
  obtain ⟨active⟩ := nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler
    13 (nativeStart bit) (aliceActivated bit) (.activate alice) initial (by
      change _ ∈ (PMF.pure (.activate alice : nativeApp.Command)).support
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) (by
      rw [initial_activation]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact nativeMenu.trace_respond nativeInitialLaw nativeHorizon nativeScheduler 13
    (aliceActivated bit) alice nativeSilent active (native_silent_available _ _ _)

theorem quiet_watcher_trace (bit : Bool) :
    Nonempty (nativeArena.Trace
      (some ⟨12, none, watcherRespond bit nativeSilent ∅ nativeSilent⟩)) := by
  obtain ⟨previous⟩ := quiet_ambient_trace bit
  obtain ⟨active⟩ := nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler
    12 (ambientRespond bit nativeSilent) (watcherActivated bit nativeSilent ∅)
    (.activate watcher) previous (by
      change _ ∈ (PMF.pure (.activate watcher : nativeApp.Command)).support
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) (by
      rw [quiet_watcher_activation]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact nativeMenu.trace_respond nativeInitialLaw nativeHorizon nativeScheduler 12
    (watcherActivated bit nativeSilent ∅) watcher nativeSilent active
      (native_silent_available _ _ _)

theorem quiet_bob_trace (bit : Bool) :
    Nonempty (nativeArena.Trace (some ⟨9, some bob, quietBob bit⟩)) := by
  obtain ⟨previous⟩ := quiet_watcher_trace bit
  obtain ⟨wire⟩ := nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler
    11 (watcherRespond bit nativeSilent ∅ nativeSilent) (quietAfterWire bit) .wait previous (by
      change _ ∈ ((PMF.pure NetworkChoice.wait).map _).support
      rw [PMF.pure_map]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) (by
      rw [quiet_wire]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨granted⟩ := nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler
    10 (quietAfterWire bit) (quietGranted bit) (.application (.grant bobPublication)) wire (by
      change _ ∈ (PMF.pure (.application (.grant bobPublication) : nativeApp.Command)).support
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) (by
      rw [quiet_grant]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  exact nativeMenu.trace_environment nativeInitialLaw nativeHorizon nativeScheduler
    9 (quietGranted bit) (quietBob bit) (.activate bob) granted (by
      change _ ∈ (PMF.pure (.activate bob : nativeApp.Command)).support
      exact (PMF.mem_support_pure_iff _ _).mpr rfl) (by
      rw [quiet_bob_activation]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)

def quietBobHistory (bit : Bool) : nativeArena.History :=
  ⟨some ⟨9, some bob, quietBob bit⟩, (quiet_bob_trace bit).some⟩

theorem quiet_bob_history_info (bit : Bool) :
    nativeModel.infoOf bob (quietBobHistory bit).trace = quietBobInfo := by
  exact (nativeMenu.info nativeInitialLaw nativeHorizon nativeScheduler bob
    (quietBobHistory bit).trace).trans (quiet_bob_info bit)

def quietBobSite : nativeModel.InformationSite bob := by
  refine ⟨quietBobInfo, ⟨⟨quietBobHistory false, quiet_bob_history_info false⟩, ?_, ?_⟩⟩
  · simp [quietBobHistory, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal]
  · refine ⟨nativeSilent, ?_⟩
    change ∃ action ∈ nativeMenu.actions bob [] ((quietBob false).observe nativeApp bob),
      some nativeSilent = some action
    exact ⟨nativeSilent, native_silent_available _ _ _, rfl⟩

theorem decode_native_alice :
    nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon nativeScheduler
      alice nativeAliceBehavior) = nativeAlicePolicy := by
  apply nativeMenu.decode_restrictPolicy_of_covered
  intro past view response supported
  cases (PMF.mem_support_pure_iff _ _).mp supported
  exact native_alice_available past view

theorem decode_native_watcher :
    nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon nativeScheduler
      watcher nativeWatcherBehavior) = nativeWatcherPolicy := by
  apply nativeMenu.decode_restrictPolicy_of_covered
  intro past view response supported
  cases (PMF.mem_support_pure_iff _ _).mp supported
  exact native_watcher_available past view

private theorem control_step_environment (players : Player → nativeApp.Policy)
    (execution next : nativeApp.Execution) (remaining : Nat) (command : nativeApp.Command)
    (selected : nativeScheduler execution.environmentRecall
      (execution.observeEnvironment nativeApp) = PMF.pure command)
    (moved : execution.environmentStep nativeApp command = PMF.pure next) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨remaining + 1, none, execution⟩) =
      PMF.pure (some ⟨remaining, command.actor? nativeApp, next⟩) := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
    ReactiveApplication.transition, selected, PMF.pure_bind, moved, PMF.pure_map]

private theorem control_step_player (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (remaining : Nat) (who : Player) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨remaining, some who, execution⟩) =
      (players who (execution.recall who) (execution.observe nativeApp who)).map fun action =>
        some ⟨remaining, none, execution.respond nativeApp who action⟩ := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
    ReactiveApplication.transition, ite_true, Option.getD_some, ← PMF.bind_pure_comp,
        Function.comp_def]

private theorem quiet_step_initial (players : Player → nativeApp.Policy) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players none =
      (PMF.uniformOfFintype Bool).map
        (fun bit => some ⟨14, none, nativeStart bit⟩) := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_none,
    ReactiveApplication.transition, nativeInitialLaw, PMF.map_comp]
  rfl

private theorem quiet_step_alice (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨14, none, nativeStart bit⟩) =
      PMF.pure (some ⟨13, some alice, aliceActivated bit⟩) :=
  control_step_environment players _ _ 13 (.activate alice) rfl (initial_activation bit)

private theorem quiet_step_alice_response (players : Player → nativeApp.Policy)
    (prescribed : ∀ bit, players alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice) = PMF.pure nativeSilent) (bit : Bool) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨13, some alice, aliceActivated bit⟩) =
      PMF.pure (some ⟨13, none, ambientRespond bit nativeSilent⟩) := by
  rw [control_step_player, prescribed]
  change (PMF.pure nativeSilent).map _ = _
  exact PMF.pure_map _ _

private theorem quiet_step_watcher (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨13, none, ambientRespond bit nativeSilent⟩) =
      PMF.pure (some ⟨12, some watcher, watcherActivated bit nativeSilent ∅⟩) :=
  control_step_environment players _ _ 12 (.activate watcher) rfl (quiet_watcher_activation bit)

private theorem quiet_step_watcher_response (players : Player → nativeApp.Policy)
    (prescribed : ∀ bit, players watcher ((watcherActivated bit nativeSilent ∅).recall watcher)
      ((watcherActivated bit nativeSilent ∅).observe nativeApp watcher) =
        PMF.pure nativeSilent) (bit : Bool) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨12, some watcher, watcherActivated bit nativeSilent ∅⟩) =
      PMF.pure (some ⟨12, none, watcherRespond bit nativeSilent ∅ nativeSilent⟩) := by
  rw [control_step_player, prescribed]
  change (PMF.pure nativeSilent).map _ = _
  exact PMF.pure_map _ _

private theorem quiet_step_wire (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨12, none, watcherRespond bit nativeSilent ∅ nativeSilent⟩) =
      PMF.pure (some ⟨11, none, quietAfterWire bit⟩) := by
  apply control_step_environment players _ _ 11 .wait _ (quiet_wire bit)
  change (PMF.pure NetworkChoice.wait).map _ = PMF.pure _
  exact PMF.pure_map _ _

private theorem quiet_step_grant (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨11, none, quietAfterWire bit⟩) =
      PMF.pure (some ⟨10, none, quietGranted bit⟩) :=
  control_step_environment players _ _ 10 (.application (.grant bobPublication)) rfl
    (quiet_grant bit)

private theorem quiet_step_bob (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players
      (some ⟨10, none, quietGranted bit⟩) =
      PMF.pure (some ⟨9, some bob, quietBob bit⟩) :=
  control_step_environment players _ _ 9 (.activate bob) rfl (quiet_bob_activation bit)

theorem quiet_bob_control_law (players : Player → nativeApp.Policy)
    (alicePolicy : ∀ bit, players alice ((aliceActivated bit).recall alice)
      ((aliceActivated bit).observe nativeApp alice) = PMF.pure nativeSilent)
    (watcherPolicy : ∀ bit, players watcher ((watcherActivated bit nativeSilent ∅).recall watcher)
      ((watcherActivated bit nativeSilent ∅).observe nativeApp watcher) =
        PMF.pure nativeSilent) :
    (fun distribution => distribution.bind
      (nativeApp.controlStep nativeInitialLaw nativeHorizon nativeScheduler players))^[8]
        (PMF.pure none) =
      (PMF.uniformOfFintype Bool).map
        (fun bit => some ⟨9, some bob, quietBob bit⟩) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    PMF.pure_bind, quiet_step_initial, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind,
        quiet_step_alice,
    quiet_step_alice_response players alicePolicy, quiet_step_watcher,
    quiet_step_watcher_response players watcherPolicy, quiet_step_wire, quiet_step_grant,
    quiet_step_bob]

theorem quiet_bob_history_law (profile : Profile nativeModel.behavioralSignature)
    (alicePolicy : profile alice = nativeAliceBehavior)
    (watcherPolicy : profile watcher = nativeWatcherBehavior) :
    (nativeModel.runBehavioral profile 8).map History.state =
      (PMF.uniformOfFintype Bool).map
        (fun bit => some ⟨9, some bob, quietBob bit⟩) := by
  rw [InformationModel.runBehavioral, nativeMenu.run_map_controlStep]
  apply quiet_bob_control_law
  · intro bit
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler alice (profile alice)) _ _ = _
    rw [alicePolicy, decode_native_alice]
    rfl
  · intro bit
    change nativeApp.decodePolicy (nativeMenu.embedPolicy nativeInitialLaw nativeHorizon
      nativeScheduler watcher (profile watcher)) _ _ = _
    rw [watcherPolicy, decode_native_watcher]
    rfl

end Vegas.Examples.MonitoredGuessing
