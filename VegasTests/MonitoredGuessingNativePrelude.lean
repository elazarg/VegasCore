/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNative
import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactiveResponseObservation
import Vegas.Pending.ReactiveStateInvariant
import Interaction.MessageNetworkInvariant
import Interaction.ReactiveRoundTrace

/-! # The monitored prefix preserves the initialized application

The rejection facts quantify arbitrary raw packets and candidate catalogues.
They use the actual compiled publication barrier: Alice cannot settle her
publication before Bob. Watcher owns neither event.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def bobBindingRef : EventGraph.FieldRef nativeGraph.layout (.binding bob .bool) :=
  ⟨.inl bobInput, rfl⟩

def aliceBindingRef : EventGraph.FieldRef nativeGraph.layout (.binding alice .bool) :=
  ⟨.inl aliceInput, rfl⟩

theorem bob_node : nodeView nativeGraph bobPublication =
    .resolve bob .bool bobBindingRef [] rfl rfl := rfl

theorem alice_node : nodeView nativeGraph alicePublication =
    .resolve alice .bool aliceBindingRef [] rfl rfl := rfl

/-- Neither Alice nor Watcher can change the application before Bob's event,
even with arbitrary hidden preparation, application data, or attached evidence. -/
theorem prelude_rejects (bit : Bool) (state : State nativeGraph)
    (initialConfig : state.config = (nativeInitial bit).config)
    (message : Message Player (Payload nativeGraph)) (notBob : message.sender ≠ bob) :
    handle nativeRuntime state message = none := by
  have blocked : ¬ state.config.cut.Ready alicePublication := by
    rw [initialConfig]
    exact initial_alice_not_ready bit
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => rfl
  | commitment event candidate =>
      fin_cases event
      · simp only [handle, bob_node]
        split_ifs <;> rfl
      · simp only [handle, blocked, ↓reduceDIte]
  | opening event candidate raw =>
      fin_cases event
      · simp only [handle, bob_node]
        split_ifs <;> simp_all [Message.sender]
      · simp only [handle, blocked, ↓reduceDIte]
  | withhold event =>
      fin_cases event
      · simp only [handle, bob_node]
        split_ifs <;> simp_all [Message.sender]
      · simp only [handle, blocked, ↓reduceDIte]

def nativeStart (bit : Bool) : nativeApp.Execution :=
  ReactiveApplication.Execution.initial nativeApp (nativeInitial bit)

theorem native_initial_trace (bit : Bool) :
    Nonempty (nativeArena.Trace (some ⟨14, none, nativeStart bit⟩)) := by
  refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
  · constructor
    · change ¬False
      trivial
    · intro who
      change ¬ (none : Option Player) = some who
      simp
  · change _ ∈ (nativeInitialLaw.map _).support
    rw [FinDist.support_map]
    refine ⟨nativeInitial bit, ?_, rfl⟩
    rw [nativeInitialLaw, FinDist.support_map]
    exact ⟨bit, FinDist.mem_support_uniformOfFintype bit, rfl⟩

def aliceActivated (bit : Bool) : nativeApp.Execution :=
  { nativeStart bit with environmentRecall :=
      [⟨(nativeStart bit).observeEnvironment nativeApp, .activate alice⟩] }

def ambientRespond (bit : Bool) (action : nativeApp.Action) : nativeApp.Execution :=
  (aliceActivated bit).respond nativeApp alice action

def watcherActivated (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) : nativeApp.Execution :=
  let previous := ambientRespond bit action
  { previous with
    network := previous.network.learn watcher selected
    environmentRecall := previous.environmentRecall ++
      [⟨previous.observeEnvironment nativeApp, .activate watcher⟩] }

def watcherRespond (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) (reply : nativeApp.Action) :
    nativeApp.Execution := (watcherActivated bit action selected).respond nativeApp watcher reply

theorem initial_activation (bit : Bool) :
    (nativeStart bit).environmentStep nativeApp (.activate alice) =
      FinDist.pure (aliceActivated bit) := by
  simp [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    nativeLeaks, alice, watcher, bob, MessageNetwork.learn_empty,
    FinDist.map_pure, aliceActivated, nativeStart, ReactiveApplication.Execution.initial]

theorem ambient_config (bit : Bool) (action : nativeApp.Action) :
    (ambientRespond bit action).application.config = (nativeInitial bit).config := by
  exact (nativeRuntime.reactive_respond_application nativeLeaks (aliceActivated bit)
    alice action).1

theorem watcher_config (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) (reply : nativeApp.Action) :
    (watcherRespond bit action selected reply).application.config =
      (nativeInitial bit).config := by
  exact (nativeRuntime.reactive_respond_application nativeLeaks
    (watcherActivated bit action selected) watcher reply).1.trans (ambient_config bit action)

private theorem respond_not_bob (execution : nativeApp.Execution)
    (who : Player) (different : who ≠ bob) (action : nativeApp.Action)
    (prior : execution.network.Satisfies (fun message => message.sender ≠ bob)) :
    (execution.respond nativeApp who action).network.Satisfies
      (fun message => message.sender ≠ bob) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact prior
  | some transmission =>
      cases transmission with
      | submit submission => exact prior.submit who _ different
      | replay id => exact prior.replay who id

theorem watcher_no_bob_packet (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) (reply : nativeApp.Action) :
    (watcherRespond bit action selected reply).network.Satisfies
      (fun message => message.sender ≠ bob) := by
  apply respond_not_bob _ watcher (by decide) reply
  apply MessageNetwork.Satisfies.learn
  exact respond_not_bob _ alice (by decide) action MessageNetwork.Satisfies.empty

/-- All possible inclusions at the report stage leave the application unchanged;
this includes Watcher's own raw deviations, not just the prescribed replay. -/
theorem prelude_include_application (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) (reply : nativeApp.Action)
    (id : MessageId Player) :
    ((watcherRespond bit action selected reply).includePending nativeApp id).application =
      (watcherRespond bit action selected reply).application := by
  let execution := watcherRespond bit action selected reply
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : execution.network.lookup id with
  | none => rfl
  | some message =>
      have rejected : nativeApp.handle execution.application message = none :=
        prelude_rejects bit execution.application (watcher_config bit action selected reply)
          ⟨message.id, message.payload.call⟩
          ((watcher_no_bob_packet bit action selected reply).lookup id message found)
      change (nativeApp.handle execution.application message).getD execution.application = _
      rw [rejected]
      rfl

theorem prelude_include_config (bit : Bool) (action : nativeApp.Action)
    (selected : Finset (MessageId Player)) (reply : nativeApp.Action)
    (id : MessageId Player) :
    ((watcherRespond bit action selected reply).includePending nativeApp id).application.config =
      (nativeInitial bit).config := by
  rw [prelude_include_application]
  exact watcher_config bit action selected reply

end VegasTests.MonitoredGuessing
