/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeHistory

/-! # The receiver's native decision depth

The service makes two player responses before activating Bob. This counts
actual legal transitions, including arbitrary raw responses and passive reads.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private def earlyActivations (count : Nat) : Nat :=
  if count = 0 then 0 else if count = 1 then 1 else if count ≤ 4 then 2 else 3

private theorem early_scheduler_count (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (early : history.length ≤ 4) :
    earlyActivations (history.length + 1) = earlyActivations history.length +
      (command.actor? nativeApp).toList.length := by
  generalize size : history.length = count at *
  interval_cases count
  · unfold nativeScheduler at supported
    rw [size] at supported
    change command ∈ (FinDist.pure (.activate alice : nativeApp.Command)).support at supported
    cases FinDist.mem_support_pure.mp supported
    rfl
  · unfold nativeScheduler at supported
    rw [size] at supported
    change command ∈ (FinDist.pure (.activate watcher : nativeApp.Command)).support at supported
    cases FinDist.mem_support_pure.mp supported
    rfl
  · unfold nativeScheduler at supported
    rw [size] at supported
    change command ∈ (nativeRuntime.interactionInstruction nativeLeaks nativeNetwork history
      view .wire).support at supported
    simp only [interactionInstruction, nativeNetwork, FinDist.map_pure,
      FinDist.mem_support_pure] at supported
    subst command
    cases last : view.network.inputs.getLast? with
    | none => simp [NetworkChoice.command, ReactiveApplication.atMostOnceCommand,
        ReactiveApplication.Command.actor?, earlyActivations]
    | some input =>
        by_cases report : input.broadcaster = watcher ∧ input.envelope.sender = alice
        · simp only [ite_eq_left report, NetworkChoice.command]
          change earlyActivations 3 = earlyActivations 2 +
            ((if view.Unpublished nativeApp input.envelope.id then
              ReactiveApplication.Command.include input.envelope.id else
                ReactiveApplication.Command.wait).actor? nativeApp).toList.length
          split <;> rfl
        · simp [report, NetworkChoice.command, ReactiveApplication.atMostOnceCommand,
            ReactiveApplication.Command.actor?, earlyActivations]
  · unfold nativeScheduler at supported
    rw [size] at supported
    change command ∈ (FinDist.pure
      (.application (.grant bobPublication) : nativeApp.Command)).support at supported
    cases FinDist.mem_support_pure.mp supported
    rfl
  · unfold nativeScheduler at supported
    rw [size] at supported
    change command ∈ (FinDist.pure (.activate bob : nativeApp.Command)).support at supported
    cases FinDist.mem_support_pure.mp supported
    rfl

private def EarlyDepth (state : nativeApp.ProtocolState) (depth : Nat) : Prop :=
  match state with
  | none => depth = 0
  | some control => control.execution.environmentRecall.length ≤ 5 →
      depth + control.actor.toList.length = 1 + control.execution.environmentRecall.length +
        earlyActivations control.execution.environmentRecall.length

private theorem early_trace_count :
    ∀ {state} (trace : nativeArena.Trace state), EarlyDepth state trace.length
  | _, .start => rfl
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited : EarlyDepth source before.length := early_trace_count before
      have reached : target ∈ (nativeApp.transition nativeInitialLaw nativeHorizon
          nativeScheduler source joint).support := realized
      cases source with
      | none =>
          obtain ⟨initial, _, rfl⟩ := FinDist.support_map .. ▸ reached
          have counted : before.length = 0 := inherited
          simpa only [EarlyDepth, Trace.length, ReactiveApplication.Execution.initial,
            List.length_nil, Option.toList_none, Nat.add_zero, earlyActivations,
            ↓reduceIte, Nat.zero_le, forall_const] using congrArg (· + 1) counted
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases FinDist.mem_support_pure.mp reached
              intro early
              have counted := inherited
                (by simpa only [nativeApp.respond_environmentRecall] using early)
              simpa only [Trace.length, nativeApp.respond_environmentRecall,
                Option.toList_some, Option.toList_none, List.length_singleton,
                List.length_nil, Nat.add_zero] using counted
          | none =>
              cases remaining with
              | zero =>
                  have stopped := legal.1
                  exact (stopped ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
                  intro early
                  have schedulerRecall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment nativeApp, command⟩] := by
                    obtain ⟨updated, _, equal⟩ := FinDist.support_map .. ▸ supported
                    cases equal
                    rfl
                  have previousEarly : execution.environmentRecall.length ≤ 4 := by
                    rw [schedulerRecall, List.length_append, List.length_singleton] at early
                    omega
                  have counted := inherited
                    (show execution.environmentRecall.length ≤ 5 by omega)
                  have activations := early_scheduler_count execution.environmentRecall
                    (execution.observeEnvironment nativeApp) command selected previousEarly
                  simp only [Option.toList_none, List.length_nil, Nat.add_zero] at counted
                  simp only [Trace.length, schedulerRecall, List.length_append,
                    List.length_singleton, activations]
                  omega

theorem native_bob_depth (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some bob) :
    trace.length = 8 := by
  have position := (native_bob_remaining control trace active).1
  have counted := early_trace_count trace
    (show control.execution.environmentRecall.length ≤ 5 by omega)
  rw [position, active] at counted
  norm_num [earlyActivations] at counted
  omega

theorem native_bob_information_depth (site : nativeModel.InformationSite bob)
    (history : nativeModel.InformationHistory bob site.1) : history.1.trace.length = 8 := by
  have active := InformationModel.InformationSite.active nativeModel site history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  cases state with
  | none => cases active
  | some control => exact native_bob_depth control trace active

end VegasTests.MonitoredGuessing
