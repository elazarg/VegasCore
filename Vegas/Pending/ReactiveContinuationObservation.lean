/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveObservedState
import Vegas.Pending.EventExpiryObservation

/-! # Owner-local submission and maintenance laws -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem State.playerView_observation_eq (left right : State graph) (who : Player)
    (views : left.playerView who = right.playerView who) :
    graph.playerObserve who left.config = graph.playerObserve who right.config := by
  have observed := congrArg (fun view : PlayerView graph =>
    (view.observation.completionOrder, view.observation.store, view.observation.ownActions)) views
  apply PlayerObservation.ext graph
  · exact congrArg Prod.fst observed
  · exact congrArg (fun value => value.2.1) observed
  · exact congrArg (fun value => value.2.2) observed

theorem Submission.register_playerView_congr (submission : Submission graph)
    (left right : State graph) (who : Player)
    (views : left.playerView who = right.playerView who) :
    (submission.register left who).playerView who =
      (submission.register right who).playerView who := by
  rcases submission with ⟨packet, opening⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot with
      | initial input => exact views
      | prepared serial =>
          cases opening with
          | none => exact views
          | some raw =>
              by_cases same : owner = who
              · simp only [Submission.register, same, ↓reduceIte]
                exact privateStep_focal_playerView_congr left right who (.prepare serial raw)
                  (congrArg PlayerView.publicView views)
                  (left.playerView_observation_eq right who views)
                  (congrArg PlayerView.remembered views) (congrArg PlayerView.candidates views)
              · simpa only [Submission.register, ite_eq_right same] using views
  | opening event candidate raw | withhold event | malformed raw =>
      cases opening <;> exact views

theorem submit_playerView_congr (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : State graph) (who : Player) (submission : WitnessedSubmission graph)
    (views : left.playerView who = right.playerView who) :
    ((runtime.reactiveApplication leaks).submit left who submission).playerView who =
      ((runtime.reactiveApplication leaks).submit right who submission).playerView who := by
  have registered := submission.call.register_playerView_congr left right who views
  have publicEq := congrArg PlayerView.publicView registered
  have observed := State.playerView_observation_eq _ _ who registered
  have remembered := congrArg PlayerView.remembered registered
  have candidates := submitStep_candidates_congr _ _ who submission.call.packet
    (congrArg PlayerView.candidates registered)
  change (submitStep _ who _).playerView who = (submitStep _ who _).playerView who
  unfold State.playerView
  simp only [submitStep_publicView, submitStep_config, submitStep_remembered]
  congr 1

/-- Envelope counters authenticate transport identity but do not enter application handling. -/
theorem handle_serial_irrel (runtime : EventGraphRuntime graph) (state : State graph)
    (who : Player) (first second : Nat) (packet : Payload graph) :
    handle runtime state ⟨(who, first), packet⟩ =
      handle runtime state ⟨(who, second), packet⟩ := by
  cases packet <;> rfl

theorem handle_result_playerView_congr (runtime : EventGraphRuntime graph)
    (left right : State graph) (who : Player) (first second : Nat) (packet : Payload graph)
    (views : left.playerView who = right.playerView who) :
    ((handle runtime left ⟨(who, first), packet⟩).getD left).playerView who =
      ((handle runtime right ⟨(who, second), packet⟩).getD right).playerView who := by
  rw [handle_serial_irrel runtime right who second first]
  have same := handle_playerView_congr_of_sender runtime left right who
    ⟨(who, first), packet⟩ views rfl
  cases a : handle runtime left ⟨(who, first), packet⟩ <;>
    cases b : handle runtime right ⟨(who, first), packet⟩ <;>
    simp only [a, b, Option.map_none, Option.map_some] at same
  · exact views
  · cases same
  · cases same
  · exact Option.some.inj same

/-- Clocks, grants and failure expiry preserve equality of the owner's view. -/
theorem maintenance_playerView_congr (runtime : EventGraphRuntime graph)
    (left right : State graph) (who : Player) (command : EnvironmentCommand graph)
    (maintenance : ∀ event, command ≠ .executeSample event)
    (views : left.playerView who = right.playerView who) :
    (environmentStep runtime left command).map (fun next => next.playerView who) =
      (environmentStep runtime right command).map (fun next => next.playerView who) := by
  have publicEq : left.publicView = right.publicView := congrArg PlayerView.publicView views
  have observed := left.playerView_observation_eq right who views
  have remembered := congrArg PlayerView.remembered views
  have candidates := congrArg PlayerView.candidates views
  cases command with
  | executeSample event => exact (maintenance event rfl).elim
  | advanceClock =>
      simp only [environmentStep, FinDist.map_pure]
      congr 1
      change { left.playerView who with
        publicView := { left.publicView with clock := left.clock + 1 } } =
        { right.playerView who with
          publicView := { right.publicView with clock := right.clock + 1 } }
      have clocks : left.clock = right.clock := congrArg PublicView.clock publicEq
      rw [views, publicEq, clocks]
  | grant event =>
      simp only [environmentStep, FinDist.map_pure]
      congr 1
      change { left.playerView who with
        publicView := { left.publicView with serviceGrant := some event } } =
        { right.playerView who with
          publicView := { right.publicView with serviceGrant := some event } }
      rw [views, publicEq]
  | expire event =>
      obtain ⟨a, ha⟩ := (environmentStep runtime left (.expire event)).support_nonempty
      obtain ⟨b, hb⟩ := (environmentStep runtime right (.expire event)).support_nonempty
      have same := environmentStep_expire_playerView_congr runtime who event left right a b
        publicEq observed remembered candidates ha hb
      simp only [environmentStep, FinDist.mem_support_pure] at ha hb
      subst a
      subst b
      simpa only [environmentStep, FinDist.map_pure] using congrArg FinDist.pure same

end Vegas.EventGraphRuntime
