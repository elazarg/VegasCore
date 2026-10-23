/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning

/-! # The message readout of a reactive execution

The readout retains message observations, responses and emitted envelopes,
including unpublished ones. Private application fields are absent. It is an
auxiliary proof readout, not a public observation or new state.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

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

end Interaction.ReactiveApplication
