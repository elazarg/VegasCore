/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventApplication
import Vegas.Pending.ExclusionCompletion
import Vegas.EventGraph.ObservationStep

/-! # Native observations of paired graph completions -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Freezing a common handle preserves equality of one player's candidate
catalogue. The two foreign catalogues need not agree. -/
theorem candidates_accept_observe_congr
    (left right : CommitmentCandidates Player (CandidateSlot graph) (Raw L))
    (focal : Player) (candidate : Handle graph)
    (observations : (fun slot => left.lookup (focal, slot)) =
      fun slot => right.lookup (focal, slot)) :
    (fun slot => (left.freeze candidate).lookup (focal, slot)) =
      fun slot => (right.freeze candidate).lookup (focal, slot) := by
  funext slot
  by_cases same : (focal, slot) = candidate
  · subst candidate
    rw [CommitmentCandidates.lookup_freeze_self, CommitmentCandidates.lookup_freeze_self,
      congrFun observations slot]
  · rw [CommitmentCandidates.lookup_freeze_other _ _ _ same,
      CommitmentCandidates.lookup_freeze_other _ _ _ same, congrFun observations slot]

/-- Equal native player views remain equal when the same public acceptance
cell and opaque candidate handle are installed on both sides. -/
theorem State.acceptHandle_playerView_congr (left right : State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (field : graph.Field) (candidate : Handle graph) :
    ({ left with
        accepted := Function.update left.accepted field (some candidate)
        candidates := left.candidates.freeze candidate } : State graph).playerView focal =
      ({ right with
          accepted := Function.update right.accepted field (some candidate)
          candidates := right.candidates.freeze candidate } : State graph).playerView focal := by
  have publicEq := congrArg PlayerView.publicView views
  have observed := left.playerView_observation_eq right focal views
  have candidatesEq := candidates_accept_observe_congr left.candidates right.candidates
    focal candidate (congrArg PlayerView.candidates views)
  have acceptedEq := congrArg PublicView.accepted publicEq
  have publicObserved := congrArg PublicView.observation publicEq
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  unfold State.playerView State.publicView
  congr 1
  congr 1
  exact congrArg (fun accepted => Function.update accepted field (some candidate)) acceptedEq

/-- A completion's public result, default entry and own action determine its
observation effect. Native clocks add no dependence on foreign hidden bindings. -/
theorem State.complete_playerView_congr (left right : State graph) (focal : Player)
    (publicEq : left.publicView = right.publicView)
    (observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config)
    (candidatesEq : (fun slot => left.candidates.lookup (focal, slot)) =
      fun slot => right.candidates.lookup (focal, slot))
    (event : graph.EventId) (leftReady : left.config.cut.Ready event)
    (rightReady : right.config.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value)
    (values : graph.fieldVisibleTo focal (.inr event) → leftValue = rightValue)
    (actions : graph.actor? event = some focal → leftAction = rightAction)
    (publicEffect :
      (Completion.fromDecision event
        (left.config.actualDecision event leftAction) leftValue).defaultEvent =
      (Completion.fromDecision event
        (right.config.actualDecision event rightAction) rightValue).defaultEvent) :
    (left.complete event leftReady leftAction leftValue).playerView focal =
      (right.complete event rightReady rightAction rightValue).playerView focal := by
  have observed := playerObserve_complete_congr focal left.config right.config observationEq
    event leftReady rightReady leftAction rightAction leftValue rightValue values actions
    publicEffect
  have publicObserved := publicObserve_eq_of_playerObserve_eq focal _ _ observed
  have cuts := cut_eq_of_completionOrder_eq _ _
    (congrArg PlayerObservation.completionOrder observed)
  have acceptedEq := congrArg PublicView.accepted publicEq
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  have nextActivated :
      State.refreshActivated (left.config.complete event leftReady leftAction leftValue)
          left.clock left.activatedAt =
        State.refreshActivated (right.config.complete event rightReady rightAction rightValue)
          right.clock right.activatedAt := by
    funext query
    simp only [State.refreshActivated, cuts]
    rw [show left.clock = right.clock from clockEq,
      show left.activatedAt = right.activatedAt from activatedEq]
  have nextPublic : (left.complete event leftReady leftAction leftValue).publicView =
      (right.complete event rightReady rightAction rightValue).publicView := by
    unfold State.publicView State.complete
    congr 1
  unfold State.playerView
  change PlayerView.mk focal _ _ _ = PlayerView.mk focal _ _ _
  rw [nextPublic]
  dsimp only [State.complete]
  rw [observed, candidatesEq]

end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime.State

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Automatic eligibility depends only on the publicly retained frontier and defaults. -/
theorem automaticReady_congr (left right : State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal) (event : graph.EventId) :
    left.AutomaticReady event ↔ right.AutomaticReady event := by
  have observations := left.playerView_observation_eq right focal views
  have cuts := cut_eq_of_completionOrder_eq left.config right.config
    (congrArg PlayerObservation.completionOrder observations)
  have defaults : left.config.defaulted = right.config.defaulted :=
    congrArg PlayerObservation.defaulted observations
  unfold AutomaticReady
  rw [cuts, defaults]

/-- Paired mechanical failure completions reveal no extra hidden information. -/
theorem completeFailure_playerView_congr (left right : State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal) (event : graph.EventId)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event) :
    (left.completeFailure event leftReady).playerView focal =
      (right.completeFailure event rightReady).playerView focal := by
  have publicEq := congrArg PlayerView.publicView views
  have observations := left.playerView_observation_eq right focal views
  have candidatesEq := congrArg PlayerView.candidates views
  have defaults : left.config.defaulted = right.config.defaulted :=
    congrArg PlayerObservation.defaulted observations
  cases node : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      simp only [completeFailure, node]
      apply complete_playerView_congr left right focal publicEq observations candidatesEq
        event leftReady rightReady
      · exact fun _ => rfl
      · exact fun _ => rfl
      · rw [left.config.completion_bind_none_defaultEvent event owner payload outputEq codeEq,
          right.config.completion_bind_none_defaultEvent event owner payload outputEq codeEq,
          defaults]
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [completeFailure, node]
      apply complete_playerView_congr left right focal publicEq observations candidatesEq
        event leftReady rightReady
      · exact fun _ => rfl
      · exact fun _ => rfl
      · rw [left.config.completion_resolve_defaultEvent event owner payload binding checks
          outputEq codeEq, right.config.completion_resolve_defaultEvent event owner payload
          binding checks outputEq codeEq, defaults]
  | sample payload law outputEq codeEq =>
      simpa only [completeFailure, node] using views

/-- Paired automatic completions preserve the focal player's complete native view. -/
theorem completeAutomatic_playerView_congr (left right : State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal) (event : graph.EventId)
    (leftEligible : left.AutomaticReady event) (rightEligible : right.AutomaticReady event) :
    (left.completeAutomatic event leftEligible).playerView focal =
      (right.completeAutomatic event rightEligible).playerView focal :=
  completeFailure_playerView_congr left right focal views event leftEligible.1 rightEligible.1

private theorem choose_eq_of_predicate_eq {α : Type} (left right : α → Prop)
    (same : left = right) (leftExists : ∃ value, left value)
    (rightExists : ∃ value, right value) :
    Classical.choose leftExists = Classical.choose rightExists := by
  cases same
  rfl

/-- Bounded automatic service is a congruence of the complete native player view. -/
theorem drainFuel_playerView_congr (fuel : Nat) (left right : State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal) :
    (drainFuel fuel left).playerView focal = (drainFuel fuel right).playerView focal := by
  induction fuel generalizing left right with
  | zero => exact views
  | succ fuel ih =>
      have predicates : left.AutomaticReady = right.AutomaticReady := by
        funext event
        exact propext (automaticReady_congr left right focal views event)
      by_cases leftPending : ∃ event, left.AutomaticReady event
      · have rightPending : ∃ event, right.AutomaticReady event := by
          rwa [← predicates]
        have chosen := choose_eq_of_predicate_eq left.AutomaticReady right.AutomaticReady
          predicates leftPending rightPending
        simp only [drainFuel, dite_eq_left leftPending, dite_eq_left rightPending]
        apply ih
        have rightEligible : right.AutomaticReady (Classical.choose leftPending) := by
          rw [chosen]
          exact Classical.choose_spec rightPending
        have paired := completeAutomatic_playerView_congr left right focal views
          (Classical.choose leftPending) (Classical.choose_spec leftPending) rightEligible
        simpa only [chosen] using paired
      · have rightClear : ¬ ∃ event, right.AutomaticReady event := by
          rwa [← predicates]
        simpa only [drainFuel, dite_eq_right leftPending, dite_eq_right rightClear] using views

/-- Full automatic service uses the same public fuel and preserves equal native views. -/
theorem drain_playerView_congr (left right : State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal) :
    left.drain.playerView focal = right.drain.playerView focal := by
  have observations := left.playerView_observation_eq right focal views
  have cuts := cut_eq_of_completionOrder_eq left.config right.config
    (congrArg PlayerObservation.completionOrder observations)
  have fuel : left.config.remaining = right.config.remaining := by
    unfold EventGraph.Config.remaining
    rw [cuts]
  unfold drain
  rw [fuel]
  exact drainFuel_playerView_congr _ left right focal views

end Vegas.EventGraphRuntime.State
