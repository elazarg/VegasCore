/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedReplay
import VegasTests.PendingSource

/-! # Exact replay cylinders on a compiled two-player source

One honest registration constrains exactly one assignment coordinate. The
other player remains an arbitrary native deviator; unused coordinates are
unconstrained. These tests concern full proof-facing executions, not equality
of the observations that omit the honest private registration.
-/

noncomputable section

namespace VegasTests.SealedReplay

open Vegas Vegas.EventGraph Interaction GameTheory.Math.Probability
open PendingSource

abbrev Value := Option Bool
abbrev app := sealedFragment.compile.messageApplication (Value := Value)

def initial : app.PolicyExecution :=
  MessageApplication.PolicyExecution.initial app
    (MessageApplication.State.initial app ⟨IdealCommitments.empty, []⟩)

def registered (value : Value) : app.PolicyExecution :=
  { initial with
    native := { initial.native with
      application.service := (IdealCommitments.empty.sealValue 0 0 value).state }
    principalHistory := fun who => if who = 0 then
      [⟨MessageApplication.State.observe app initial.native 0, .privateCommand ⟨(0, value)⟩⟩]
      else []
    nativeTrace := [.privateCommand 0 ⟨(0, value)⟩] }

theorem assigned_first_command (values : Fin graph.nodeCount → Value) :
    sealedFragment.playerPolicy 0 (sealedFragment.valuePolicy values 0) []
      (MessageApplication.State.observe app initial.native 0) =
        FinDist.pure (.privateCommand ⟨(0, values (node 0))⟩) := by
  change sealedFragment.commitCommand 0 (sealedFragment.valuePolicy values 0)
    (node 0) _ rfl [] _ = _
  unfold SealedFragment.commitCommand
  simp only [MessageApplication.ChoiceEncoding.cachedValue_nil]
  change (FinDist.pure _).map _ = _
  simp only [FinDist.map_pure, cast_eq]
  rfl

theorem first_native_law (values : Fin graph.nodeCount → Value)
    (deviator : app.PlayerPolicy) (environment : app.EnvironmentPolicy) :
    app.runPolicies (sealedFragment.valuePlayers values 1 deviator) environment
      [.player 0] initial = FinDist.pure (registered (values (node 0))) := by
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, FinDist.bind_pure]
  rw [SealedFragment.valuePlayers, GameTheory.Profile.update_of_ne _ _ (by decide)]
  change (sealedFragment.playerPolicy 0 (sealedFragment.valuePolicy values 0) []
    (MessageApplication.State.observe app initial.native 0)).bind _ = _
  rw [assigned_first_command, FinDist.pure_bind]
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
  rfl

theorem first_replay (values : Fin graph.nodeCount → Value)
    (deviator : List app.PlayerEntry → app.View → app.PlayerCommand)
    (environment : List app.EnvironmentEntry → app.EnvironmentObservation →
      app.EnvironmentPolicyCommand) :
    sealedFragment.replay values 1 deviator environment [.player 0] =
      registered (values (node 0)) := by
  have h := sealedFragment.replay_law values 1 deviator environment [.player 0]
  change app.runPolicies (sealedFragment.valuePlayers values 1
    (fun history view => FinDist.pure (deviator history view)))
    (fun history view => FinDist.pure (environment history view)) [.player 0] initial = _ at h
  rw [first_native_law] at h
  have hmem : registered (values (node 0)) ∈
      (FinDist.pure (sealedFragment.replay values 1 deviator environment [.player 0])).support := by
    rw [← h, FinDist.mem_support_pure]
  exact (FinDist.mem_support_pure.mp hmem).symm

/-- This cylinder contains every assignment with the observed first value;
neither the focal coordinate nor the reveal coordinates are constrained. -/
theorem first_replay_eq_iff (left right : Fin graph.nodeCount → Value)
    (deviator : List app.PlayerEntry → app.View → app.PlayerCommand)
    (environment : List app.EnvironmentEntry → app.EnvironmentObservation →
      app.EnvironmentPolicyCommand) :
    sealedFragment.replay left 1 deviator environment [.player 0] =
        sealedFragment.replay right 1 deviator environment [.player 0] ↔
      left (node 0) = right (node 0) := by
  rw [sealedFragment.replay_eq_iff]
  constructor
  · intro h
    exact h 0 (node 0) (left (node 0)) (by decide)
      (by rw [first_replay]; exact List.mem_singleton_self _)
  · intro h owner index value _ htrace
    rw [first_replay] at htrace
    change (.privateCommand owner ⟨(index.val, value)⟩ : app.Action) ∈
      [.privateCommand 0 ⟨(0, left (node 0))⟩] at htrace
    have heq := List.mem_singleton.mp htrace
    have hslot := congrArg (fun command : app.Action => match command with
      | .privateCommand _ request => request.down.1
      | _ => 0) heq
    have hindex : index = node 0 := Fin.ext hslot
    simpa only [hindex] using h

end VegasTests.SealedReplay

/-- info: 'VegasTests.SealedReplay.first_replay_eq_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedReplay.first_replay_eq_iff
