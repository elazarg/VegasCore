/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRounds
import Interaction.ReactiveMessageReadout

/-! # Reactive round congruence from its actual component kernels -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Including pending traffic leaves every player's recorded responses fixed. -/
theorem Execution.includePending_recall (execution : app.Execution) (id : MessageId Principal) :
    (execution.includePending app id).recall = execution.recall := by
  unfold Execution.includePending
  generalize execution.network.includePending id = pair
  rcases pair with ⟨_ | _, _⟩ <;> rfl

/-- An environment move retains any auxiliary readout determined by own recall. -/
theorem Execution.environmentStep_map_pair_of_recall {Value Auxiliary : Type*}
    (execution : app.Execution) (command : app.Command)
    (read : app.Execution → Value) (auxiliary : app.Execution → Auxiliary)
    (kept : ∀ next, next.recall = execution.recall → auxiliary next = auxiliary execution) :
    (execution.environmentStep app command).map (fun next => (read next, auxiliary next)) =
      ((execution.environmentStep app command).map read).map
        (fun value => (value, auxiliary execution)) := by
  rw [PMF.map_comp]
  apply map_congr_on_support _
  intro next supported
  exact Prod.ext rfl (kept next (app.environmentStep_recall execution next command supported))

/-- Equal scheduler inputs, shared activation samples, response kernels at each
sample, and the remaining environment kernels determine the mapped round law. -/
theorem round_map_congr {Value : Type*} (scheduler : app.Scheduler)
    (first second : Principal → app.Policy) (left right : app.Execution)
    (read : app.Execution → Value)
    (recall : left.environmentRecall = right.environmentRecall)
    (observed : left.observeEnvironment app = right.observeEnvironment app)
    (networks : left.network = right.network)
    (activation : ∀ actor,
      (.activate actor : app.Command) ∈
        (scheduler right.environmentRecall (right.observeEnvironment app)).support →
      ∀ sample ∈ (app.observePending actor right.network.pending).support,
        let leftActive := left.sampledActivation app actor sample
        let rightActive := right.sampledActivation app actor sample
        ((first actor (leftActive.recall actor) (leftActive.observe app actor)).map
          (leftActive.respond app actor)).map read =
        ((second actor (rightActive.recall actor) (rightActive.observe app actor)).map
          (rightActive.respond app actor)).map read)
    (environment : ∀ command ∈
      (scheduler right.environmentRecall (right.observeEnvironment app)).support,
      command.actor? app = none →
      (left.environmentStep app command).map read =
        (right.environmentStep app command).map read) :
    (app.round scheduler first left).map read = (app.round scheduler second right).map read := by
  unfold round
  rw [recall, observed, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro command selected
  cases command with
  | activate actor =>
      simp only [dispatch, Command.actor?, resume, invoke, Execution.activation_samples,
        PMF.bind_map, PMF.map_bind, Function.comp_def]
      rw [networks]
      apply bind_congr_on_support _
      intro sample supported
      exact activation actor selected sample supported
  | «include» id | application command | wait =>
      change ((left.environmentStep app _).bind (fun execution => PMF.pure execution)).map read =
        ((right.environmentStep app _).bind (fun execution => PMF.pure execution)).map read
      simpa only [PMF.bind_pure] using
        environment _ selected rfl

end Interaction.ReactiveApplication
