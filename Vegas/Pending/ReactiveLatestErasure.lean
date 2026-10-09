/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePriorityErasure
import Vegas.Pending.ReactiveLateBlind
import Vegas.Pending.ReactiveServiceSelection

/-! # Erasure independence of deterministic addressed inclusion

The last eligible pending envelope selector either includes an erased
identifier or selects exactly the same retained identifier in both worlds.
This statement holds for arbitrary public inputs, without provenance or
message uniqueness assumptions. It does not extend to an arbitrary mixture
of this selector and waiting.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}

private theorem latest_identifier_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView)
    (predicate : Message Player (runtime.reactiveApplication leaks).Payload → Bool)
    (same : ∀ message, predicate message = true ↔
      message.sender = owner ∧ message.payload.call.event? graph = some event ∧
        view.Unpublished (runtime.reactiveApplication leaks) message.id) :
    runtime.reactiveLatest leaks event owner view =
      ((view.network.pending.reverse.find? predicate).map Message.id).elim
        (ReactiveApplication.Command.wait : (runtime.reactiveApplication leaks).Command)
          ReactiveApplication.Command.include := by
  unfold reactiveLatest
  have representation (selected : Option (Message Player (runtime.reactiveApplication
    leaks).Payload)) :
      (match selected with
      | none => (ReactiveApplication.Command.wait : (runtime.reactiveApplication leaks).Command)
      | some message => ReactiveApplication.Command.include message.id) =
        (selected.map Message.id).elim ReactiveApplication.Command.wait
          ReactiveApplication.Command.include := by
    cases selected <;> rfl
  refine (representation _).trans ?_
  apply congrArg (fun selected : Option (Message Player (runtime.reactiveApplication
    leaks).Payload) =>
    (selected.map Message.id).elim
      (ReactiveApplication.Command.wait : (runtime.reactiveApplication leaks).Command)
        ReactiveApplication.Command.include)
  apply congrArg (fun flag : Message Player (runtime.reactiveApplication leaks).Payload → Bool =>
    view.network.pending.reverse.find? flag)
  funext message
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (same message).symm

/-- Removing an unselected pending identifier leaves the deterministic
addressed selection unchanged after restoring identifiers. -/
theorem reactiveLatest_restore_of_not_selected (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) (removed : MessageId Player)
    (notSelected : runtime.reactiveLatest leaks event owner view ≠ .include removed) :
    ReactiveApplication.Command.restore (runtime.reactiveApplication leaks) removed
      (runtime.reactiveLatest leaks event owner
        (view.erase (runtime.reactiveApplication leaks) removed)) =
      runtime.reactiveLatest leaks event owner view := by
  let before := fun message : Message Player (runtime.reactiveApplication leaks).Payload =>
    decide (message.sender = owner ∧ message.payload.call.event? graph = some event ∧
      view.Unpublished (runtime.reactiveApplication leaks) message.id)
  let after := fun message : Message Player (runtime.reactiveApplication leaks).Payload =>
    decide (message.sender = owner ∧ message.payload.call.event? graph = some event ∧
      (view.erase (runtime.reactiveApplication leaks) removed).Unpublished
        (runtime.reactiveApplication leaks) message.id)
  have predicate : ∀ message : Message Player (runtime.reactiveApplication leaks).Payload,
    message.id ≠ removed →
      after ⟨MessageId.erase removed message.id, message.payload⟩ = before message := by
    intro message kept
    simp only [before, after, Message.sender, MessageId.erase_author,
      ReactiveApplication.EnvironmentView.unpublished_erase
        (runtime.reactiveApplication leaks) view removed message.id kept]
  have original := latest_identifier_law runtime leaks event owner view before (by
    intro message
    simp only [before, decide_eq_true_eq])
  have erased := latest_identifier_law runtime leaks event owner
    (view.erase (runtime.reactiveApplication leaks) removed) after (by
      intro message
      simp only [after, decide_eq_true_eq])
  have unselected : (view.network.pending.reverse.find? before).map Message.id ≠ some removed := by
    intro selected
    apply notSelected
    rw [original, selected]
    rfl
  have identifiers := Message.find_eraseList_restore removed before after predicate
    view.network.pending.reverse unselected
  have reversed : Message.eraseList removed view.network.pending.reverse =
      (Message.eraseList removed view.network.pending).reverse := by
    exact Message.eraseList_reverse removed view.network.pending
  rw [reversed] at identifiers
  have command := congrArg (fun id : Option (MessageId Player) =>
    id.elim (ReactiveApplication.Command.wait : (runtime.reactiveApplication leaks).Command)
      ReactiveApplication.Command.include) identifiers
  rw [original, erased]
  change ReactiveApplication.Command.restore (runtime.reactiveApplication leaks) removed
    ((((Message.eraseList removed view.network.pending).reverse.find? after).map Message.id).elim
      ReactiveApplication.Command.wait ReactiveApplication.Command.include) =
    ((view.network.pending.reverse.find? before).map Message.id).elim
      ReactiveApplication.Command.wait ReactiveApplication.Command.include
  cases first : view.network.pending.reverse.find? before <;>
    cases second : (Message.eraseList removed view.network.pending).reverse.find? after
  all_goals first
  | rfl
  | simpa only [first, second, Option.map_none, Option.map_some, Option.elim_none,
      Option.elim_some, ReactiveApplication.Command.restore] using command

/-- Deterministic addressed selection is a mixture of selecting an erased
identifier and its command in the erased world. The mixture coefficient is
zero or one; arbitrary public packet contents and duplicate identifiers are
allowed. -/
theorem reactiveLatest_include_or_erased (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (owner : Player)
    (view : (runtime.reactiveApplication leaks).EnvironmentView) (removed : MessageId Player) :
    ∃ (probability : ℝ) (nonnegative : 0 ≤ probability) (atMost : probability ≤ 1),
      PMF.pure (runtime.reactiveLatest leaks event owner view) =
        mix probability nonnegative atMost (PMF.pure (.include removed))
          ((PMF.pure (runtime.reactiveLatest leaks event owner
            (view.erase (runtime.reactiveApplication leaks) removed))).map
              (ReactiveApplication.Command.restore (runtime.reactiveApplication leaks) removed))
                := by
  classical
  by_cases selected : runtime.reactiveLatest leaks event owner view = .include removed
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [mix_one, selected]
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    rw [mix_zero, PMF.pure_map, runtime.reactiveLatest_restore_of_not_selected
      leaks event owner view removed selected]

end Vegas.EventGraphRuntime
