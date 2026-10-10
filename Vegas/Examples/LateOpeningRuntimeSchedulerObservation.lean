/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeService

/-! # Observable metadata implements the native late-opening scheduler

The actual service command law uses its round counter, ordered pending
identifiers, ledger identifiers and the public binding-completion flag.
Envelope payloads, submitted-input contents, private catalogues and submission
counters are absent from this observation. The equality holds at every view,
including views produced by arbitrary raw responses.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeService

open SourceProgram EventGraph EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource

structure SchedulerObservation where
  round : Nat
  pending : List (MessageId Player)
  published : List (MessageId Player)
  bindingComplete : Bool

def schedulerObservation (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : SchedulerObservation :=
  ⟨past.length, view.network.pending.map Message.id, view.network.ledger.map Message.id,
    decide (bobBindEvent ∈ view.application.observation.completionOrder)⟩

def observableLatestAuthor (who : Player) (observation : SchedulerObservation) : app.Command :=
  ((observation.pending.reverse.find? (fun id =>
    id.1 = who ∧ id ∉ observation.published))).elim .wait .include

private theorem find_author_id (who : Player)
    (pending : List (Message Player (WitnessedPacket nativeGraph)))
    (published : List (MessageId Player)) :
    (pending.find? (fun message => message.sender = who ∧ message.id ∉ published)).map
        Message.id =
      (pending.map Message.id).find? (fun id => id.1 = who ∧ id ∉ published) := by
  induction pending with
  | nil => rfl
  | cons message rest ih =>
      by_cases allowed : message.sender = who ∧ message.id ∉ published
      · simp [List.find?_cons, Message.sender] at *
      · simp [List.find?_cons, Message.sender] at *

theorem latestAuthor_eq_observable (who : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    latestAuthor who view = observableLatestAuthor who (schedulerObservation past view) := by
  change latestAuthor who view =
    (((view.network.pending.map Message.id).reverse.find? (fun id =>
      id.1 = who ∧ id ∉ view.network.ledger.map Message.id))).elim .wait .include
  rw [← List.map_reverse]
  have mapped := congrArg (fun selected : Option (MessageId Player) =>
      selected.elim (ReactiveApplication.Command.wait (app := app)) .include)
    (find_author_id who view.network.pending.reverse (view.network.ledger.map Message.id))
  calc
    latestAuthor who view =
        ((view.network.pending.reverse.find? (fun message =>
          message.sender = who ∧ message.id ∉ view.network.ledger.map Message.id)).map
            Message.id).elim .wait .include := by
      unfold latestAuthor
      simp only [ReactiveApplication.EnvironmentView.Unpublished]
      generalize view.network.pending.reverse.find? _ = found
      cases found <;> rfl
    _ = _ := mapped

def observableStageChoice (weight : ℝ) (nonnegative : 0 ≤ weight)
    (observation : SchedulerObservation) : PMF app.Command :=
  match observation.round with
  | 0 | 3 | 7 => PMF.pure (.activate alice)
  | 1 => PMF.pure (observableLatestAuthor alice observation)
  | 4 | 11 | 19 => PMF.pure (.activate bob)
  | 5 | 12 | 20 => PMF.pure (observableLatestAuthor bob observation)
  | 8 => (MessageNetwork.chooseWithOutside weight nonnegative observation.pending.toFinset).map
      (fun selected => selected.elim .wait .include)
  | 10 => PMF.pure (.application (.expire aliceEvent))
  | 13 => PMF.pure (if observation.bindingComplete then .activate bob else .wait)
  | 14 => PMF.pure (if observation.bindingComplete
      then observableLatestAuthor bob observation else .wait)
  | 18 => PMF.pure (.application (.expire bobBindEvent))
  | 25 => PMF.pure (.application (.expire bobRevealEvent))
  | 2 | 6 | 9 | 15 | 16 | 17 | 21 | 22 | 23 | 24 => PMF.pure (.application .advanceClock)
  | _ => PMF.pure .wait

theorem scheduler_observation_factorization (weight : ℝ) (nonnegative : 0 ≤ weight)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) :
    scheduler weight nonnegative past view =
      observableStageChoice weight nonnegative (schedulerObservation past view) := by
  have latest (who : Player) : latestAuthor who view =
      (((view.network.pending.map Message.id).reverse.find? (fun id =>
        id.1 = who ∧ id ∉ view.network.ledger.map Message.id))).elim .wait .include := by
    exact latestAuthor_eq_observable who past view
  simp only [scheduler, observableStageChoice, schedulerObservation, observableLatestAuthor]
  unfold stageChoice
  split <;> simp_all [ReactiveApplication.pendingLotteryScheduler,
    ReactiveApplication.Scheduler.ofObservation, MessageNetwork.pendingIds]
  rfl

theorem scheduler_eq_of_observation_eq (weight : ℝ) (nonnegative : 0 ≤ weight)
    {firstPast secondPast : List app.EnvironmentEntry}
    {firstView secondView : app.EnvironmentView}
    (same : schedulerObservation firstPast firstView =
      schedulerObservation secondPast secondView) :
    scheduler weight nonnegative firstPast firstView =
      scheduler weight nonnegative secondPast secondView := by
  rw [scheduler_observation_factorization, scheduler_observation_factorization, same]

theorem runRounds_observable_scheduler (weight : ℝ) (nonnegative : 0 ≤ weight)
    (players : Player → app.Policy) (count : Nat) (execution : app.Execution) :
    app.runRounds (scheduler weight nonnegative) players count execution =
      app.runRounds (ReactiveApplication.Scheduler.ofObservation app schedulerObservation
        (observableStageChoice weight nonnegative)) players count execution :=
  app.runRounds_eq_of_scheduler_factorization _ _ _
    (scheduler_observation_factorization weight nonnegative) players count execution

end Vegas.Examples.LateOpeningRuntimeService
