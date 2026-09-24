/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveOwnerSelection
import Vegas.Pending.ReactiveServiceSelection
import Vegas.Pending.ReactiveContinuationObservation

/-! # Reconstructing reserved selection from an owner's information

With at most one distinct owner envelope addressed to an event, arbitrary
rebroadcasting changes no reserved choice. Its identity is determined by own
output recall and the publicly recorded envelope identities.
-/

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

theorem interaction_includeLatest_environment
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    runtime.interactionStep leaks players network (.includeLatest event who) execution =
      execution.environmentStep (runtime.reactiveApplication leaks)
        (runtime.reactiveLatest leaks event who
          (execution.observeEnvironment (runtime.reactiveApplication leaks))) := by
  simp only [interactionStep, interactionInstruction,
    GameTheory.Math.Probability.FinDist.pure_bind, ReactiveApplication.dispatch]
  have inactive : (runtime.reactiveLatest leaks event who
      (execution.observeEnvironment (runtime.reactiveApplication leaks))).actor?
        (runtime.reactiveApplication leaks) = none := by
    unfold reactiveLatest
    split <;> rfl
  rw [inactive]
  change (_ : GameTheory.Math.Probability.FinDist _).bind
    GameTheory.Math.Probability.FinDist.pure = _
  exact GameTheory.Math.Probability.FinDist.bind_pure _

theorem reactiveLatest_step_pure (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    ∃ next, execution.environmentStep (runtime.reactiveApplication leaks)
      (runtime.reactiveLatest leaks event who
        (execution.observeEnvironment (runtime.reactiveApplication leaks))) =
          GameTheory.Math.Probability.FinDist.pure next := by
  unfold reactiveLatest
  split <;> simp only [ReactiveApplication.Execution.environmentStep,
    GameTheory.Math.Probability.FinDist.map_pure]
  all_goals exact ⟨_, rfl⟩

theorem reactive_include_playerView (execution : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : execution.network.lookup id = some message) :
    ((execution.environmentStep (runtime.reactiveApplication leaks) (.include id)).map
      fun next => next.application.playerView who) =
      GameTheory.Math.Probability.FinDist.pure
        (((handle runtime execution.application ⟨message.id, message.payload.call⟩).getD
          execution.application).playerView who) := by
  simp only [ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found,
    GameTheory.Math.Probability.FinDist.map_pure]
  rfl

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
  | some transmission =>
      cases transmission with
      | submit material =>
          exact runtime.submit_playerView_congr leaks left.application right.application who
            material views
      | replay id =>
          cases first : (left.network.known who).find? (fun message => message.id = id) <;>
            cases second : (right.network.known who).find? (fun message => message.id = id) <;>
            simpa only [ReactiveApplication.Execution.respond, MessageNetwork.replay,
              first, second] using views

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
older envelope unchanged, including arbitrary replay responses. -/
theorem reactiveLatest_nonmatching_response (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (origins : execution.Provenance (runtime.reactiveApplication leaks))
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (retained : execution.network.PendingOrPublished)
    (unique : runtime.UniqueEventOutput leaks who event (execution.recall who))
    (response : (runtime.reactiveApplication leaks).Action)
    (nonmatching : ∀ material, response.transmission = some (.submit material) →
      material.call.packet.event? graph ≠ some event) :
    runtime.reactiveLatest leaks event who
      ((execution.respond (runtime.reactiveApplication leaks) who response).observeEnvironment
        (runtime.reactiveApplication leaks)) =
      runtime.reactiveLatest leaks event who
        (execution.observeEnvironment (runtime.reactiveApplication leaks)) := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material =>
          have different := nonmatching material rfl
          simp only [reactiveLatest, ReactiveApplication.Execution.respond,
            ReactiveApplication.Execution.observeEnvironment, MessageNetwork.submit,
            MessageNetwork.publicView, List.reverse_append, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.singleton_append, List.find?_cons,
            reactiveApplication, WitnessedSubmission.emit_call, different,
            and_false, false_and, decide_false]
          rfl
      | replay id =>
          have selected := (runtime.reactiveApplication leaks).find_pending_replay_from_recall
            execution who who id
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
          cases found : (execution.network.known who).find? (fun message => message.id = id) <;>
            simp only [MessageNetwork.replay, found] at selected
          all_goals
            simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]
          · rfl
          · exact congrArg (fun chosen :
                Option (Message Player (runtime.reactiveApplication leaks).Payload) =>
              match chosen with
              | none => (ReactiveApplication.Command.wait :
                  (runtime.reactiveApplication leaks).Command)
              | some message => .include message.id) selected

theorem reactive_reserved_nonmatching_playerView (who : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (origins : execution.Provenance (runtime.reactiveApplication leaks))
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (retained : execution.network.PendingOrPublished)
    (unique : runtime.UniqueEventOutput leaks who event (execution.recall who))
    (response : (runtime.reactiveApplication leaks).Action)
    (audit : (execution.respond (runtime.reactiveApplication leaks) who response).SubmissionAudit
      (runtime.reactiveApplication leaks) ReactivePlayerView.publicView)
    (nonmatching : ∀ material, response.transmission = some (.submit material) →
      material.call.packet.event? graph ≠ some event) :
    let after := execution.respond (runtime.reactiveApplication leaks) who response
    ((after.environmentStep (runtime.reactiveApplication leaks)
      (runtime.reactiveLatest leaks event who
        (after.observeEnvironment (runtime.reactiveApplication leaks)))).map
          fun next => next.application.playerView who) =
      GameTheory.Math.Probability.FinDist.pure
        (match ((runtime.reactiveApplication leaks).outputs (execution.recall who)).find?
          (fun message => message.sender = who ∧ message.payload.call.event? graph = some event ∧
            (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
              (runtime.reactiveApplication leaks) message.id) with
        | none => after.application.playerView who
        | some message => ((handle runtime after.application
            ⟨message.id, message.payload.call⟩).getD after.application).playerView who) := by
  dsimp only
  rw [runtime.reactiveLatest_nonmatching_response leaks who event execution origins recalled
    retained unique response nonmatching]
  rw [runtime.reactiveLatest_from_recall leaks who event execution origins recalled retained unique]
  cases selected : ((runtime.reactiveApplication leaks).outputs (execution.recall who)).find?
      (fun message => message.sender = who ∧ message.payload.call.event? graph = some event ∧
        (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
          (runtime.reactiveApplication leaks) message.id) with
  | none =>
      simp only [ReactiveApplication.Execution.environmentStep,
        GameTheory.Math.Probability.FinDist.map_pure]
  | some message =>
      have good : message.sender = who ∧ message.payload.call.event? graph = some event ∧
          (execution.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
            (runtime.reactiveApplication leaks) message.id := by
        have qualifying := List.find?_some selected
        simpa only [decide_eq_true_eq] using qualifying
      have pending := ((runtime.reactiveApplication leaks).pending_iff_recalled execution who
        message good.1 good.2.2 origins recalled retained).mpr
          (List.mem_of_find?_eq_some selected)
      have stillPending := (runtime.reactiveApplication leaks).respond_pending_mono execution
        who response pending
      exact runtime.reactive_include_playerView leaks _ who message.id message
        (audit.lookup_of_mem (runtime.reactiveApplication leaks) ReactivePlayerView.publicView
          _ message stillPending)

/-- With a unique older event output, every current raw response has an
owner-local immediate inclusion effect. New matching submissions override
the older envelope; silence, wrong-address calls, and replays use it unchanged. -/
theorem reactive_reserved_playerView_congr (who : Player) (event : graph.EventId)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (response : (runtime.reactiveApplication leaks).Action)
    (views : left.application.playerView who = right.application.playerView who)
    (recalls : left.recall who = right.recall who)
    (ledgers : left.network.ledger = right.network.ledger)
    (leftOrigins : left.Provenance (runtime.reactiveApplication leaks))
    (rightOrigins : right.Provenance (runtime.reactiveApplication leaks))
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (leftRetained : left.network.PendingOrPublished)
    (rightRetained : right.network.PendingOrPublished)
    (leftUnique : runtime.UniqueEventOutput leaks who event (left.recall who))
    (rightUnique : runtime.UniqueEventOutput leaks who event (right.recall who))
    (leftSerials : left.network.SerialsBeforeNext)
    (rightSerials : right.network.SerialsBeforeNext)
    (leftAudit : (left.respond (runtime.reactiveApplication leaks) who response).SubmissionAudit
      (runtime.reactiveApplication leaks) ReactivePlayerView.publicView)
    (rightAudit : (right.respond (runtime.reactiveApplication leaks) who response).SubmissionAudit
      (runtime.reactiveApplication leaks) ReactivePlayerView.publicView) :
    let afterLeft := left.respond (runtime.reactiveApplication leaks) who response
    let afterRight := right.respond (runtime.reactiveApplication leaks) who response
    ((afterLeft.environmentStep (runtime.reactiveApplication leaks)
      (runtime.reactiveLatest leaks event who
        (afterLeft.observeEnvironment (runtime.reactiveApplication leaks)))).map
          fun next => next.application.playerView who) =
    ((afterRight.environmentStep (runtime.reactiveApplication leaks)
      (runtime.reactiveLatest leaks event who
        (afterRight.observeEnvironment (runtime.reactiveApplication leaks)))).map
          fun next => next.application.playerView who) := by
  dsimp only
  have afterViews := runtime.reactive_respond_playerView_congr leaks left right who response views
  by_cases matching : ∃ material, response.transmission = some (.submit material) ∧
      material.call.packet.event? graph = some event
  · obtain ⟨material, transmitted, addressed⟩ := matching
    rcases response with ⟨transmission⟩
    cases transmitted
    rw [runtime.reactiveLatest_after_submit leaks who event left leftSerials material addressed,
      runtime.reactiveLatest_after_submit leaks who event right rightSerials material addressed]
    have lookup (execution : (runtime.reactiveApplication leaks).Execution)
        (serials : execution.network.SerialsBeforeNext) :
        (execution.respond (runtime.reactiveApplication leaks) who
          ⟨some (.submit material)⟩).network.lookup (who, execution.network.nextSerial who) =
          some ⟨(who, execution.network.nextSerial who), material.emit
            ((runtime.reactiveApplication leaks).submit execution.application who material)
              who (execution.network.known who)⟩ := serials.lookup_submit who _
    rw [runtime.reactive_include_playerView leaks _ who _ _ (lookup left leftSerials),
      runtime.reactive_include_playerView leaks _ who _ _ (lookup right rightSerials)]
    exact congrArg GameTheory.Math.Probability.FinDist.pure
      (runtime.handle_result_playerView_congr _ _ who (left.network.nextSerial who)
        (right.network.nextSerial who) material.call.packet afterViews)
  · have nonmatching : ∀ material, response.transmission = some (.submit material) →
        material.call.packet.event? graph ≠ some event := by
      intro material transmitted addressed
      exact matching ⟨material, transmitted, addressed⟩
    rw [runtime.reactive_reserved_nonmatching_playerView leaks who event left leftOrigins
      leftRecall leftRetained leftUnique response leftAudit nonmatching,
      runtime.reactive_reserved_nonmatching_playerView leaks who event right rightOrigins
        rightRecall rightRetained rightUnique response rightAudit nonmatching]
    have selections :
        ((runtime.reactiveApplication leaks).outputs (left.recall who)).find?
          (fun message => message.sender = who ∧ message.payload.call.event? graph = some event ∧
            (left.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
              (runtime.reactiveApplication leaks) message.id) =
        ((runtime.reactiveApplication leaks).outputs (right.recall who)).find?
          (fun message => message.sender = who ∧ message.payload.call.event? graph = some event ∧
            (right.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
              (runtime.reactiveApplication leaks) message.id) := by
      simp only [ReactiveApplication.EnvironmentView.Unpublished,
        ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView,
        recalls, ledgers]
    rw [← selections]
    cases selected : ((runtime.reactiveApplication leaks).outputs (left.recall who)).find?
        (fun message => message.sender = who ∧ message.payload.call.event? graph = some event ∧
          (left.observeEnvironment (runtime.reactiveApplication leaks)).Unpublished
            (runtime.reactiveApplication leaks) message.id) with
    | none => exact congrArg GameTheory.Math.Probability.FinDist.pure afterViews
    | some message =>
        have author : message.sender = who := by
          have good := List.find?_some selected
          exact (of_decide_eq_true good).1
        rcases message with ⟨⟨sender, serial⟩, packet⟩
        change sender = who at author
        subst sender
        exact congrArg GameTheory.Math.Probability.FinDist.pure
          (runtime.handle_result_playerView_congr _ _ who serial serial packet.call afterViews)

end Vegas.EventGraphRuntime
