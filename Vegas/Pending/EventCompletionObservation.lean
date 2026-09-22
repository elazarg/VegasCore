/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication
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
  have observationEq := congrArg
    (fun view : PlayerView graph =>
      (view.observation.completionOrder, view.observation.store, view.observation.ownActions)) views
  have observed : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config := by
    apply PlayerObservation.ext graph
    · exact congrArg Prod.fst observationEq
    · exact congrArg (fun value => value.2.1) observationEq
    · exact congrArg (fun value => value.2.2) observationEq
  have rememberedEq := congrArg PlayerView.remembered views
  have candidatesEq := candidates_accept_observe_congr left.candidates right.candidates
    focal candidate (congrArg PlayerView.candidates views)
  have acceptedEq := congrArg PublicView.accepted publicEq
  have publicObserved := congrArg PublicView.observation publicEq
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  have grantEq := congrArg PublicView.serviceGrant publicEq
  unfold State.playerView State.publicView
  congr 1
  congr 1
  exact congrArg (fun accepted => Function.update accepted field (some candidate)) acceptedEq

/-- Completing the same event exposes only its public result and the focal
player's own action. Clock activation and native service metadata introduce
no dependency on foreign hidden binding meanings. -/
theorem State.complete_playerView_congr (left right : State graph) (focal : Player)
    (publicEq : left.publicView = right.publicView)
    (observationEq : graph.playerObserve focal left.config =
      graph.playerObserve focal right.config)
    (rememberedEq : (fun query => if graph.actor? query = some focal then
      left.remembered query else none) =
      fun query => if graph.actor? query = some focal then right.remembered query else none)
    (candidatesEq : (fun slot => left.candidates.lookup (focal, slot)) =
      fun slot => right.candidates.lookup (focal, slot))
    (event : graph.EventId) (leftReady : left.config.cut.Ready event)
    (rightReady : right.config.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftValue rightValue : (graph.outputLayout event).Value)
    (values : graph.fieldVisibleTo focal (.inr event) → leftValue = rightValue)
    (actions : graph.actor? event = some focal → leftAction = rightAction) :
    (left.complete event leftReady leftAction leftValue).playerView focal =
      (right.complete event rightReady rightAction rightValue).playerView focal := by
  have observed := playerObserve_complete_congr focal left.config right.config observationEq
    event leftReady rightReady leftAction rightAction leftValue rightValue values actions
  have publicObserved := publicObserve_eq_of_playerObserve_eq focal _ _ observed
  have cuts := cut_eq_of_completionOrder_eq _ _
    (congrArg PlayerObservation.completionOrder observed)
  have acceptedEq := congrArg PublicView.accepted publicEq
  have clockEq := congrArg PublicView.clock publicEq
  have activatedEq := congrArg PublicView.activatedAt publicEq
  have grantEq := congrArg PublicView.serviceGrant publicEq
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
  change PlayerView.mk focal _ _ _ _ = PlayerView.mk focal _ _ _ _
  rw [nextPublic]
  dsimp only [State.complete]
  rw [observed, rememberedEq, candidatesEq]

end Vegas.EventGraphRuntime
