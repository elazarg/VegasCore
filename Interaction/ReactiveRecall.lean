/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveServiceInvariant
import Interaction.ReactiveEnvironmentStep

/-! # Player output recall and network input history agree

The network's record of submissions by a principal is exactly the output
remembered by that principal. The envelopes a player possesses can therefore be
computed from own recall, leaked messages, and ledger, without a separate sent
list.
-/

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def outputs (history : List app.PlayerEntry) : List (Message Principal app.Payload) :=
  history.filterMap PlayerEntry.emitted

def Execution.InputRecall (execution : app.Execution) : Prop := ∀ who,
  execution.network.inputs.filter (fun input => input.sender = who) =
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
      by_cases same : observer = who
      all_goals first
        | subst observer
          simp only [Execution.respond, ↓reduceIte]
          exact List.subset_append_left _ _
        | simpa only [Execution.respond, ite_eq_right same] using List.Subset.refl _

theorem environmentStep_recall (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    next.recall = execution.recall := by
  apply app.environmentStep_cases execution next command reached
    (predicate := fun _ next => next.recall = execution.recall)
  · rfl
  · intros; rfl
  · intro id
    cases found : execution.network.lookup id <;>
      simp only [Execution.includePending, MessageNetwork.includePending, found]
  · intros; rfl

theorem respond_recall_other (execution : app.Execution) (who observer : Principal)
    (different : observer ≠ who) (action : app.Action) :
    (execution.respond app who action).recall observer = execution.recall observer := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => simp only [Execution.respond, ite_eq_right different]
  | some transmission =>
      simp only [Execution.respond, ite_eq_right different]

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
  | some submission =>
      by_cases same : observer = who
      · subst observer
        simpa [Execution.respond, MessageNetwork.submit, outputs, Message.sender,
          List.filter_append] using congrArg (· ++ [⟨(who, execution.network.nextSerial who),
            app.packet (app.submit execution.application who submission) who
              (execution.network.known who) submission⟩]) earlier
      · simpa [Execution.respond, MessageNetwork.submit, ite_eq_right same,
          Message.sender, List.filter_append, Ne.symm same] using earlier

theorem environment_inputRecall (execution next : app.Execution) (command : app.Command)
    (valid : execution.InputRecall app)
    (reached : next ∈ (execution.environmentStep app command).support) : next.InputRecall app := by
  apply app.environmentStep_cases execution next command reached
    (predicate := fun _ next => next.InputRecall app)
  · exact valid
  · exact fun _ _ _ => valid
  · intro id
    cases found : execution.network.lookup id <;>
      simpa [Execution.InputRecall, Execution.includePending,
        MessageNetwork.includePending, found] using valid
  · exact fun _ _ _ => valid

/-- An initialized player can reconstruct every envelope it possesses from its
own input/output recall and the two message lists it observes. -/
theorem known_from_recall (execution : app.Execution) (who : Principal)
    (valid : execution.InputRecall app) :
    execution.network.known who = app.outputs (execution.recall who) ++
      execution.network.leaked who ++ execution.network.ledger := by
  simp only [MessageNetwork.known, valid who]

theorem inputRecallInvariant (scheduler : app.Scheduler) :
    app.ServiceInvariant scheduler (fun execution => execution.InputRecall app) where
  respond := app.respond_inputRecall
  environment execution next command valid _ reached :=
    app.environment_inputRecall execution next command valid reached

theorem history_inputRecall (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) {state : app.ProtocolState}
    (trace : (app.protocol initial horizon scheduler).Trace state) :
    serviceInvariant (fun execution => execution.InputRecall app) state :=
  (app.inputRecallInvariant scheduler).history initial horizon
    (fun state _ => app.initial_inputRecall state) trace

end Interaction.ReactiveApplication
