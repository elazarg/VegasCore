/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.PendingPriority
import Interaction.ReactiveAllocation
import GameTheoryExtensions.Core.RegularChoiceSimulation

/-! # Regular selection after arbitrary atomic responses

The selector filters out published identifiers and deduplicates pending copies.
Its priority distribution and eligibility predicate are fixed for the response
being compared. Silence and every rebroadcast preserve its law. Submitting a
fresh envelope can only increase that identifier's probability, even for an
ineligible packet. This concerns one selection, not an adaptive service's full
continuation law.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def prioritySelection (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution) :
    FinDist (Option (MessageId Principal)) :=
  MessageNetwork.priorityPending priorities (execution.network.unpublished eligible)
    execution.network.pending

def submitsEligible (eligible : Message Principal app.Payload → Bool)
    (execution : app.Execution) (who : Principal) (action : app.Action) : Bool :=
  match action.transmission with
  | some (.submit submission) => execution.network.unpublished eligible
      (execution.network.submit who (app.packet submission)).1
  | _ => false

theorem prioritySelection_replay
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (retained : execution.network.PendingOrPublished) (who : Principal)
    (memory : app.Memory) (id : MessageId Principal) :
    app.prioritySelection priorities eligible
        (execution.respond app who ⟨memory, some (.replay id)⟩) =
      app.prioritySelection priorities eligible execution := by
  unfold prioritySelection MessageNetwork.priorityPending
  exact congrArg (GameTheory.Math.Probability.PriorityChoice.law priorities)
    (retained.replay_unpublished_ids eligible who id)

/-- The full candidate law has only two forms: unchanged, or insertion of the
sender's next identifier. Payload, memory, and transport multiplicity add no
third case. Eligibility and the priority distribution are held fixed. -/
theorem prioritySelection_response_eq
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (retained : execution.network.PendingOrPublished) (who : Principal)
    (action : app.Action) :
    app.prioritySelection priorities eligible (execution.respond app who action) =
      if app.submitsEligible eligible execution who action then
        PriorityChoice.law priorities (insert (who, execution.network.nextSerial who)
          (MessageNetwork.eligibleIds (execution.network.unpublished eligible)
            execution.network.pending))
      else app.prioritySelection priorities eligible execution := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id =>
          exact app.prioritySelection_replay priorities eligible execution retained who memory id
      | submit submission =>
          change MessageNetwork.priorityPending priorities (execution.network.unpublished eligible)
            (execution.network.pending ++ [_]) = _
          unfold MessageNetwork.priorityPending
          rw [MessageNetwork.eligibleIds_append]
          split <;> simp_all only [submitsEligible, MessageNetwork.submit, ↓reduceIte,
            Bool.false_eq_true,
            prioritySelection, MessageNetwork.priorityPending]

/-- The possible promoted identifier depends on the sender and existing
serial counter, independently of the response's payload or private memory. -/
theorem prioritySelection_response_regular
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (retained : execution.network.PendingOrPublished) (who : Principal)
    (action : app.Action) :
    (app.prioritySelection priorities eligible execution).RegularAt
      (app.prioritySelection priorities eligible (execution.respond app who action))
      (some (who, execution.network.nextSerial who)) := by
  rcases action with ⟨memory, transmission⟩
  cases transmission with
  | none => exact FinDist.RegularAt.refl _ _
  | some transmission =>
      cases transmission with
      | replay id =>
          rw [app.prioritySelection_replay priorities eligible execution retained who memory id]
          exact FinDist.RegularAt.refl _ _
      | submit submission =>
          change (MessageNetwork.priorityPending priorities
              (execution.network.unpublished eligible) execution.network.pending).RegularAt
            (MessageNetwork.priorityPending priorities (execution.network.unpublished eligible)
              (execution.network.submit who (app.packet submission)).2.pending)
            (some (execution.network.submit who (app.packet submission)).1.id)
          unfold MessageNetwork.priorityPending
          change (GameTheory.Math.Probability.PriorityChoice.law priorities _).RegularAt
            (GameTheory.Math.Probability.PriorityChoice.law priorities
              (MessageNetwork.eligibleIds _ (execution.network.pending ++ [_]))) _
          rw [MessageNetwork.eligibleIds_append]
          split
          · exact GameTheory.Math.Probability.PriorityChoice.law_regular_insert priorities _ _
          · exact FinDist.RegularAt.refl _ _

theorem prioritySelection_next_absent
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (serials : execution.network.SerialsBeforeNext) (who : Principal) :
    some (who, execution.network.nextSerial who) ∉
      (app.prioritySelection priorities eligible execution).support := by
  intro supported
  exact serials.next_not_eligible (execution.network.unpublished eligible) who
    (MessageNetwork.priorityPending_supported priorities _ _ _ supported)

/-- Decoding supplies an explicit meaning for an empty old menu. Agreement
with the application's timeout behavior is a separate obligation. -/
def priorityResponseRule {Value : Type*}
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (serials : execution.network.SerialsBeforeNext) (who : Principal)
    (decode : Option (MessageId Principal) → Value) :
    GameTheory.PendingChoice.RegularSelection Value :=
  GameTheory.PendingChoice.RegularSelection.ofInsertion
    (app.prioritySelection priorities eligible execution)
    (PriorityChoice.law priorities (insert (who, execution.network.nextSerial who)
      (MessageNetwork.eligibleIds (execution.network.unpublished eligible)
        execution.network.pending)))
    (some (who, execution.network.nextSerial who))
    (app.prioritySelection_next_absent priorities eligible execution serials who)
    (PriorityChoice.law_regular_insert priorities _ _) decode

/-- Exact decoded law for every raw player response. The fresh candidate's
meaning is supplied explicitly; the decoder of old candidates is fixed. -/
theorem prioritySelection_response_decoded {Value : Type*}
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (retained : execution.network.PendingOrPublished)
    (serials : execution.network.SerialsBeforeNext) (who : Principal)
    (decode : Option (MessageId Principal) → Value) (action : app.Action) (value : Value) :
    (app.prioritySelection priorities eligible (execution.respond app who action)).map
        (fun selected => if selected = some (who, execution.network.nextSerial who)
          then value else decode selected) =
      (app.priorityResponseRule priorities eligible execution serials who decode).includeLaw
        (if app.submitsEligible eligible execution who action then some value else none) := by
  rw [app.prioritySelection_response_eq priorities eligible execution retained who action]
  split
  · exact (GameTheory.PendingChoice.RegularSelection.ofInsertion_submit ..).symm
  · change (app.prioritySelection priorities eligible execution).map _ =
      (app.prioritySelection priorities eligible execution).map decode
    apply FinDist.map_congr_of_eq_on_support
    intro selected supported
    have different : selected ≠ some (who, execution.network.nextSerial who) :=
      fun same => app.prioritySelection_next_absent priorities eligible execution serials who
        (same ▸ supported)
    simp only [different, ↓reduceIte]

/-- Arbitrary randomized native responses share one branch law. The decoded
distribution at its fresh branch is obtained from the response distribution, without
conditioning on future inclusion or using utilities. -/
theorem prioritySelection_responses_factor {Value : Type*}
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (retained : execution.network.PendingOrPublished)
    (serials : execution.network.SerialsBeforeNext) (who : Principal)
    (decode : Option (MessageId Principal) → Value)
    (responses : FinDist app.Action) (value : app.Action → Value) :
    let rule := app.priorityResponseRule priorities eligible execution serials who decode
    (responses.bind fun action =>
      (app.prioritySelection priorities eligible (execution.respond app who action)).map
        (fun selected => if selected = some (who, execution.network.nextSerial who)
          then value action else decode selected)) =
      rule.selection.bind (fun selected => selected.elim
        (rule.translateResponses (responses.map fun action =>
          if app.submitsEligible eligible execution who action then some (value action) else none))
        FinDist.pure) := by
  dsimp only
  rw [← GameTheory.PendingChoice.RegularSelection.responseLaw_factor]
  simp only [GameTheory.PendingChoice.RegularSelection.responseLaw, FinDist.bind_map]
  apply FinDist.bind_congr
  intro action _
  exact app.prioritySelection_response_decoded priorities eligible execution retained serials
    who decode action (value action)

variable [Inhabited app.Memory]

theorem prioritySelection_history_regular
    (scheduler : app.Scheduler) (initial : FinDist app.State) (horizon : Nat)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (priorities : FinDist (LinearOrder (MessageId Principal)))
    (eligible : Message Principal app.Payload → Bool) (who : Principal) (action : app.Action) :
    (app.prioritySelection priorities eligible control.execution).RegularAt
      (app.prioritySelection priorities eligible (control.execution.respond app who action))
      (some (who, control.execution.network.nextSerial who)) :=
  app.prioritySelection_response_regular priorities eligible control.execution
    (app.pendingOrPublished_history scheduler initial horizon trace) who action

end Interaction.ReactiveApplication
