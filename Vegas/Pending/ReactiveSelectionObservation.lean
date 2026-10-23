/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOwnerSelection
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveServiceProgress
import Interaction.ReactiveAllocation
import Vegas.Pending.ReactiveContinuationObservation

/-! # Reconstructing reserved selection from an owner's information

With at most one distinct owner envelope addressed to an event, arbitrary
foreign traffic changes no reserved choice. Its identity is determined by own
output recall and the publicly recorded envelope identities.
-/

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem reactiveLatest_step_pure (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    ∃ next, execution.environmentStep (runtime.reactiveApplication leaks)
      (runtime.reactiveLatest leaks event who
        (execution.observeEnvironment (runtime.reactiveApplication leaks))) =
          PMF.pure next := by
  unfold reactiveLatest
  split <;> simp only [ReactiveApplication.Execution.environmentStep,
    PMF.pure_map]
  all_goals exact ⟨_, rfl⟩

theorem reactive_include_playerView (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : execution.network.lookup id = some message) :
    ((execution.environmentStep (runtime.reactiveApplication leaks) (.include id)).map
      fun next => next.application.playerView who) =
      PMF.pure
        ((((runtime.reactiveApplication leaks).handle execution.application
          message).getD
          execution.application).playerView who) := by
  simp only [ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found,
    PMF.pure_map]

theorem reactive_respond_playerView_congr
    (left right : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (views : left.application.playerView who = right.application.playerView who) :
    (left.respond (runtime.reactiveApplication leaks) who response).application.playerView who =
      (right.respond (runtime.reactiveApplication leaks) who response).application.playerView
        who := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact views
  | some material =>
      exact runtime.submit_playerView_congr leaks left.application right.application who
        material views

def UniqueEventOutput (who : Player) (event : graph.EventId)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry) : Prop :=
  ∀ first ∈ (runtime.reactiveApplication leaks).outputs past,
    ∀ second ∈ (runtime.reactiveApplication leaks).outputs past,
      first.sender = who → second.sender = who →
        first.payload.call.event? graph = some event →
        second.payload.call.event? graph = some event → first = second

theorem reactiveLatest_from_recall (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (origins : execution.Provenance (runtime.reactiveApplication leaks))
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (retained : execution.network.PendingOrPublished)
    (unique : runtime.UniqueEventOutput leaks who event (execution.recall who)) :
    runtime.reactiveLatest leaks event who
      (execution.observeEnvironment (runtime.reactiveApplication leaks)) =
      match ((runtime.reactiveApplication leaks).outputs (execution.recall who)).find?
        (fun message => message.sender = who ∧ message.payload.call.event? graph = some event ∧
          (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
            (runtime.reactiveApplication leaks) message.id) with
      | none => .wait
      | some message => .include message.id := by
  have selection := (runtime.reactiveApplication leaks).find_pending_from_recall execution who
    (fun message => decide (message.sender = who ∧
      message.payload.call.event? graph = some event ∧
      (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
        (runtime.reactiveApplication leaks) message.id))
    (fun _ good => (of_decide_eq_true good).1)
    (fun _ good => (of_decide_eq_true good).2.2) origins recalled retained
    (fun first firstMem second secondMem firstGood secondGood =>
      unique first firstMem second secondMem (of_decide_eq_true firstGood).1
        (of_decide_eq_true secondGood).1 (of_decide_eq_true firstGood).2.1
        (of_decide_eq_true secondGood).2.1)
  exact congrArg (fun selected :
      Option (Message Player (runtime.reactiveApplication leaks).Payload) =>
    match selected with
    | none => (ReactiveApplication.Command.wait : (runtime.reactiveApplication leaks).Command)
    | some message => .include message.id) selection

/-- A response that submits no new call to this event leaves the selected
older envelope unchanged. -/
theorem reactiveLatest_nonmatching_response (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (response : (runtime.reactiveApplication leaks).Action)
    (nonmatching : ∀ material, response.transmission = some material →
      material.call.packet.event? graph ≠ some event) :
    runtime.reactiveLatest leaks event who
      ((execution.respond (runtime.reactiveApplication leaks) who response).observeEnvironment
        (runtime.reactiveApplication leaks)) =
      runtime.reactiveLatest leaks event who
        (execution.observeEnvironment (runtime.reactiveApplication leaks)) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      have different := nonmatching material rfl
      simp only [reactiveLatest, ReactiveApplication.Execution.respond,
        ReactiveApplication.Execution.observeEnvironment, MessageNetwork.submit,
        MessageNetwork.publicView, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.singleton_append, List.find?_cons,
        reactiveApplication, WitnessedSubmission.emit_call, different,
        and_false, false_and, decide_false]
      rfl

end Vegas.EventGraphRuntime
