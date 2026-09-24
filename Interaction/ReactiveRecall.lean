/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProtocol

/-! # Player output recall and network input history agree

The network's record of broadcasts by a principal is exactly the output
remembered by that principal. Replay eligibility can therefore be computed
from own recall, leaked messages, and ledger, without a separate sent list.
-/

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def outputs (history : List app.PlayerEntry) : List (Message Principal app.Payload) :=
  history.filterMap PlayerEntry.emitted

def Execution.InputRecall (execution : app.Execution) : Prop := ∀ who,
  (execution.network.inputs.filterMap fun input =>
    if input.broadcaster = who then some input.envelope else none) =
      app.outputs (execution.recall who)

theorem respond_recall_mono (execution : app.Execution) (who observer : Principal)
    (action : app.Action) :
    execution.recall observer ⊆ (execution.respond app who action).recall observer := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      by_cases same : observer = who
      · subst observer
        simp only [Execution.respond, ↓reduceIte]
        exact List.subset_append_left _ _
      · simpa only [Execution.respond, ite_eq_right same] using List.Subset.refl _
  | some transmission =>
      cases transmission <;> by_cases same : observer = who
      all_goals first
        | subst observer
          simp only [Execution.respond, ↓reduceIte]
          exact List.subset_append_left _ _
        | simpa only [Execution.respond, ite_eq_right same] using List.Subset.refl _

theorem environmentStep_recall (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.recall = execution.recall := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      rfl
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      cases found : execution.network.lookup id <;>
        simp only [Execution.includePending, MessageNetwork.includePending, found]
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      rfl

theorem respond_recall_other (execution : app.Execution) (who observer : Principal)
    (different : observer ≠ who) (action : app.Action) :
    (execution.respond app who action).recall observer = execution.recall observer := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ite_eq_right different]
  | some transmission =>
      cases transmission <;> simp only [Execution.respond, ite_eq_right different]

theorem initial_inputRecall (state : app.State) : (Execution.initial app state).InputRecall app :=
  fun _ => rfl

theorem respond_inputRecall (execution : app.Execution) (who : Principal) (action : app.Action)
    (valid : execution.InputRecall app) : (execution.respond app who action).InputRecall app := by
  intro observer
  have earlier := valid observer
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      by_cases same : observer = who
      · subst observer
        simpa only [Execution.respond, ↓reduceIte, outputs, List.filterMap_append,
          List.filterMap_cons, List.filterMap_nil, List.append_nil] using earlier
      · simpa only [Execution.respond, ite_eq_right same] using earlier
  | some transmission =>
      cases transmission with
      | submit submission =>
          by_cases same : observer = who
          · subst observer
            simpa only [Execution.respond, MessageNetwork.submit, ↓reduceIte, outputs,
              List.filterMap_append, List.filterMap_cons, List.filterMap_nil, Option.map_some]
              using congrArg (· ++ [⟨(who, execution.network.nextSerial who),
                app.packet submission⟩]) earlier
          · simpa only [Execution.respond, MessageNetwork.submit, ite_eq_right same,
              ite_eq_right (Ne.symm same), List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, List.append_nil] using earlier
      | replay id =>
          cases knownEq : (execution.network.known who).find? (fun envelope => envelope.id = id)
          all_goals by_cases same : observer = who
          all_goals first
            | subst observer
              simpa [Execution.respond, MessageNetwork.replay, knownEq, outputs]
                using earlier
            | simpa [Execution.respond, MessageNetwork.replay, knownEq, same, Ne.symm same]
                using earlier

theorem environment_inputRecall (execution next : app.Execution) (command : app.Command)
    (valid : execution.InputRecall app)
    (reached : next ∈ (execution.environmentStep app command).support) : next.InputRecall app := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact valid
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact valid
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      cases found : execution.network.lookup id <;>
        simpa [Execution.InputRecall, Execution.includePending,
          MessageNetwork.includePending, found] using valid

/-- An initialized player can reconstruct every message eligible for replay
from its own input/output recall and the two message lists it observes. -/
theorem known_from_recall (execution : app.Execution) (who : Principal)
    (valid : execution.InputRecall app) :
    execution.network.known who = app.outputs (execution.recall who) ++
      execution.network.leaked who ++ execution.network.ledger := by
  simp only [MessageNetwork.known, valid who]

def inputRecall : app.ProtocolState → Prop
  | none => True
  | some control => control.execution.InputRecall app

theorem transition_inputRecall (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before after : app.ProtocolState)
    (joint : Principal → Option app.Action) (valid : app.inputRecall before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.inputRecall after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
      exact app.initial_inputRecall state
  | some control =>
      rcases control with ⟨remaining, current, execution⟩
      cases current with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          exact app.respond_inputRecall execution who _ valid
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
              exact app.environment_inputRecall execution next command valid moved

theorem history_inputRecall (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) :
    ∀ {state} (_trace : (app.protocol initial horizon scheduler).Trace state),
      app.inputRecall state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      app.transition_inputRecall initial horizon scheduler _ _ joint
        (history_inputRecall initial horizon scheduler prior) reached

end Interaction.ReactiveApplication
