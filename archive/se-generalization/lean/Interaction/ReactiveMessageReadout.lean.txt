/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # The message readout of a reactive execution

The readout retains message observations, responses and emitted envelopes,
including unpublished ones. Private application fields are absent. It is an
auxiliary proof readout, not a public observation or new state.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def messageRecall (past : List app.PlayerEntry) := past.map fun entry =>
  (entry.beforeView.messages, entry.beforeView.receipts, entry.action, entry.emitted)

abbrev MessageReadout :=
  MessageNetwork Principal app.Payload × List (MessageId Principal × Bool) ×
    List app.EnvironmentEntry × (Principal →
      List (MessageNetwork.PlayerView Principal app.Payload ×
        List (MessageId Principal × Bool) × app.Action × Option (Message Principal app.Payload)))

def messageView (execution : app.Execution) : app.MessageReadout :=
  (execution.network, execution.receipts, execution.environmentRecall,
    fun who => app.messageRecall (execution.recall who))

omit [DecidableEq Principal] in
theorem messageRecall_length (past : List app.PlayerEntry) :
    (app.messageRecall past).length = past.length := List.length_map ..

omit [DecidableEq Principal] in
theorem outputs_eq_of_messageRecall_eq (left right : List app.PlayerEntry)
    (same : app.messageRecall left = app.messageRecall right) :
    app.outputs left = app.outputs right := by
  have observed := congrArg (List.filterMap fun entry => entry.2.2.2) same
  simpa only [messageRecall, List.filterMap_map, outputs, Function.comp_def] using observed

/-- Materializing the same transmitted payload suffices for equality of the
complete message readout after a shared response. Private application state
and other players' private application observations may differ. -/
theorem respond_messageView_eq (left right : app.Execution) (who : Principal)
    (action : app.Action) (same : app.messageView left = app.messageView right)
    (packet : ∀ submission, action.transmission = some submission →
      app.packet (app.submit left.application who submission) who
        (left.network.known who) submission =
      app.packet (app.submit right.application who submission) who
        (right.network.known who) submission) :
    app.messageView (left.respond app who action) =
      app.messageView (right.respond app who action) := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have recalls := congrArg (fun value => value.2.2.2) same
  change left.network = right.network at networks
  change left.receipts = right.receipts at receipts
  change left.environmentRecall = right.environmentRecall at environments
  change (fun observer => app.messageRecall (left.recall observer)) =
    (fun observer => app.messageRecall (right.recall observer)) at recalls
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      apply Prod.ext networks
      apply Prod.ext receipts
      apply Prod.ext environments
      funext observer
      by_cases active : observer = who
      · subst observer
        simpa only [messageView, Execution.respond, ↓reduceIte, messageRecall,
          List.map_append, List.map_cons, List.map_nil, Execution.observe,
          networks, receipts] using congrArg (· ++
            [((right.observe app who).messages, right.receipts, (⟨none⟩ : app.Action), none)])
              (congrFun recalls who)
      · simpa only [messageView, Execution.respond, ite_eq_right active] using
          congrFun recalls observer
  | some submission =>
      have payload := packet submission rfl
      have submitted :
          left.network.submit who (app.packet (app.submit left.application who submission)
            who (left.network.known who) submission) =
          right.network.submit who (app.packet (app.submit right.application who submission)
            who (right.network.known who) submission) := by rw [payload, networks]
      rw [networks] at payload
      apply Prod.ext
      · exact congrArg (fun result => result.2) submitted
      apply Prod.ext receipts
      apply Prod.ext environments
      funext observer
      by_cases active : observer = who
      · subst observer
        simpa only [messageView, Execution.respond, ↓reduceIte, messageRecall,
          List.map_append, List.map_cons, List.map_nil, Execution.observe,
          networks, receipts, payload] using congrArg (· ++
            [((right.observe app who).messages, right.receipts,
              (⟨some submission⟩ : app.Action),
              some (right.network.submit who
                (app.packet (app.submit right.application who submission) who
                  (right.network.known who) submission)).1)]) (congrFun recalls who)
      · simpa only [messageView, Execution.respond, ite_eq_right active] using
          congrFun recalls observer

theorem respond_focal_recall_eq (left right : app.Execution) (who focal : Principal)
    (action : app.Action) (networks : left.network = right.network)
    (before : left.observe app focal = right.observe app focal)
    (recall : left.recall focal = right.recall focal)
    (packet : ∀ submission, action.transmission = some submission →
      app.packet (app.submit left.application who submission) who
        (left.network.known who) submission =
      app.packet (app.submit right.application who submission) who
        (right.network.known who) submission) :
    (left.respond app who action).recall focal =
      (right.respond app who action).recall focal := by
  by_cases active : focal = who
  · subst focal
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => simp only [Execution.respond, ↓reduceIte, recall, before]
    | some submission =>
        have payload := packet submission rfl
        rw [networks] at payload
        simp only [Execution.respond, ↓reduceIte, recall, before,
          MessageNetwork.submit, payload, networks]
  · rw [app.respond_recall_other left who focal active action,
      app.respond_recall_other right who focal active action, recall]

/-- The deterministic branch of the existing activation transition for one
sample of pending identifiers. -/
def Execution.sampledActivation (execution : app.Execution) (who : Principal)
    (selected : Finset (MessageId Principal)) : app.Execution :=
  { execution with
    network := execution.network.learn who selected
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate who⟩] }

theorem Execution.activation_samples (execution : app.Execution) (who : Principal) :
    execution.environmentStep app (.activate who) =
      (app.observePending who execution.network.pending).map
        (execution.sampledActivation app who) := by
  simp only [Execution.environmentStep, PMF.map_comp]
  rfl

theorem sampledActivation_messageView_eq (left right : app.Execution) (who : Principal)
    (selected : Finset (MessageId Principal))
    (same : app.messageView left = app.messageView right)
    (publicView : app.observePublic left.application = app.observePublic right.application) :
    app.messageView (left.sampledActivation app who selected) =
      app.messageView (right.sampledActivation app who selected) := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have recalls := congrArg (fun value => value.2.2.2) same
  change left.network = right.network at networks
  change left.receipts = right.receipts at receipts
  change left.environmentRecall = right.environmentRecall at environments
  have viewed : left.observeEnvironment app = right.observeEnvironment app := by
    simp only [Execution.observeEnvironment, networks, receipts, publicView]
  apply Prod.ext (congrArg (fun network => network.learn who selected) networks)
  apply Prod.ext receipts
  apply Prod.ext
  · exact congrArg₂ (· ++ ·) environments
      (congrArg (fun view => [(⟨view, .activate who⟩ : app.EnvironmentEntry)]) viewed)
  · exact recalls

end Interaction.ReactiveApplication
