/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.CommutationRecall
import Vegas.EventGraph.NormalizedPolicy
import Vegas.EventGraph.RevealRelaxation

/-! # Local commutation of normalized behavioral kernels

This module lifts the fixed-action event diamond to the two actual behavioral
kernels at simultaneously ready strategic events.  It composes ordinary
`Config.step` calls and does not define another graph executor.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Run two particular ready strategic events in sequence, asking each
normalized behavioral policy at the observation that actually precedes its
event.  Support evidence transports readiness across the first `Config.step`.
-/
def policyStepThen (profile : graph.BehavioralProfile) (config : graph.Config)
    (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstOwner secondOwner : Player)
    (firstActor : graph.actor? first = some firstOwner)
    (secondActor : graph.actor? second = some secondOwner) : PMF graph.Config :=
  (graph.normalizePolicy firstOwner (profile firstOwner) first firstActor
      (graph.playerObserve firstOwner config)).bind fun firstAction =>
    (config.step first firstReady firstAction).bindOnSupport fun afterFirst member =>
      (graph.normalizePolicy secondOwner (profile secondOwner) second secondActor
          (graph.playerObserve secondOwner afterFirst)).bind fun secondAction =>
        afterFirst.step second (by
          rw [config.step_cut first firstReady firstAction afterFirst member]
          exact secondReady.after_complete firstReady different.symm) secondAction

/-- What scheduler independence of a profile uses at simultaneously ready
events: distinct ready events have actors, and different ones; and completing
one of them leaves the other's normalized kernel unchanged. -/
structure ReadyIndependent (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) : Prop where
  ready_pair_actors : ∀ {cut : graph.order.Cut} {left right : graph.EventId},
    cut.Ready left → cut.Ready right → left ≠ right →
      ∃ leftOwner rightOwner,
        graph.actor? left = some leftOwner ∧
        graph.actor? right = some rightOwner ∧ leftOwner ≠ rightOwner
  normalizePolicy_complete_foreign : ∀ (config : graph.Config) (event other : graph.EventId)
    (_eventReady : config.cut.Ready event) (otherReady : config.cut.Ready other)
    {who : Player} (actor : graph.actor? event = some who) (foreign : Player),
    graph.actor? other = some foreign → foreign ≠ who →
      ∀ (action : graph.Action other) (value : (graph.outputLayout other).Value),
        graph.normalizePolicy who (profile who) event actor
            (graph.playerObserve who (config.complete other otherReady action value)) =
          graph.normalizePolicy who (profile who) event actor
            (graph.playerObserve who config)

/-- Distinct simultaneously ready events in a public-barrier graph are both
strategic, have owners, and those owners differ. A public chance/resolution
event is comparable with every other event and therefore cannot coexist. -/
theorem BarrierOrdered.ready_pair_actors
    (ordered : graph.BarrierOrdered) {cut : graph.order.Cut}
    {left right : graph.EventId} (leftReady : cut.Ready left)
    (rightReady : cut.Ready right) (different : left ≠ right) :
    ∃ leftOwner rightOwner,
      graph.actor? left = some leftOwner ∧
      graph.actor? right = some rightOwner ∧ leftOwner ≠ rightOwner :=
  (BarrierOrdered.revealRelaxedOrdered ordered).ready_pair_actors leftReady rightReady different

/-- Under public-barrier dependencies every profile is ready independent: a
simultaneously ready foreign event is a hidden binding. -/
theorem BarrierOrdered.readyIndependent (ordered : graph.BarrierOrdered)
    (profile : graph.BehavioralProfile) : graph.ReadyIndependent profile where
  ready_pair_actors := ordered.ready_pair_actors
  normalizePolicy_complete_foreign config event other eventReady otherReady _ actor foreign
      otherActor differentOwner action value :=
    (ordered.normalizePolicy_complete_foreign (profile _) config event other eventReady
      otherReady actor foreign otherActor differentOwner action value).2

/-- When the two owners differ, the second normalized kernel can be pulled
back across the first actual step.  The resulting law draws both actions from
the common pre-step information and then uses the fixed-action `stepThen`.
-/
theorem ReadyIndependent.policyStepThen_eq_independent {profile : graph.BehavioralProfile}
    (independent : graph.ReadyIndependent profile)
    (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstOwner secondOwner : Player)
    (firstActor : graph.actor? first = some firstOwner)
    (secondActor : graph.actor? second = some secondOwner)
    (differentOwner : firstOwner ≠ secondOwner) :
    policyStepThen profile config first second firstReady secondReady different
        firstOwner secondOwner firstActor secondActor =
      (graph.normalizePolicy firstOwner (profile firstOwner) first firstActor
          (graph.playerObserve firstOwner config)).bind fun firstAction =>
        (graph.normalizePolicy secondOwner (profile secondOwner) second secondActor
            (graph.playerObserve secondOwner config)).bind fun secondAction =>
          stepThen config first second firstReady secondReady different
            firstAction secondAction := by
  unfold policyStepThen
  apply bind_congr_on_support _
  intro firstAction _
  let secondLaw := graph.normalizePolicy secondOwner (profile secondOwner)
    second secondActor (graph.playerObserve secondOwner config)
  calc
    (config.step first firstReady firstAction).bindOnSupport
        (fun afterFirst member =>
          (graph.normalizePolicy secondOwner (profile secondOwner) second secondActor
              (graph.playerObserve secondOwner afterFirst)).bind fun secondAction =>
            afterFirst.step second (by
              rw [config.step_cut first firstReady firstAction afterFirst member]
              exact secondReady.after_complete firstReady different.symm) secondAction) =
      (config.step first firstReady firstAction).bindOnSupport
        (fun afterFirst member => secondLaw.bind fun secondAction =>
          afterFirst.step second (by
            rw [config.step_cut first firstReady firstAction afterFirst member]
            exact secondReady.after_complete firstReady different.symm) secondAction) := by
        apply bindOnSupport_congr _
        intro afterFirst member
        rw [Config.step, PMF.support_map] at member
        obtain ⟨value, _, rfl⟩ := member
        have stable := independent.normalizePolicy_complete_foreign config second first
          secondReady firstReady secondActor firstOwner firstActor differentOwner
          firstAction value
        exact congrArg (fun law => law.bind fun secondAction =>
          (config.complete first firstReady firstAction value).step second
            (secondReady.after_complete firstReady different.symm) secondAction) stable
    _ = secondLaw.bind fun secondAction =>
        (config.step first firstReady firstAction).bindOnSupport fun afterFirst member =>
          afterFirst.step second (by
            rw [config.step_cut first firstReady firstAction afterFirst member]
            exact secondReady.after_complete firstReady different.symm) secondAction := by
      exact (bind_bindOnSupport_comm secondLaw
        (config.step first firstReady firstAction)
        (fun secondAction afterFirst member =>
          afterFirst.step second (by
            rw [config.step_cut first firstReady firstAction afterFirst member]
            exact secondReady.after_complete firstReady different.symm) secondAction)).symm
    _ = secondLaw.bind fun secondAction =>
        stepThen config first second firstReady secondReady different
          firstAction secondAction := by
      rfl

/-- The two sequential normalized behavioral kernels commute after projecting
to the typed store and every player's original-action recall. -/
theorem ReadyIndependent.policyStepThen_map_storeRecall_comm
    {profile : graph.BehavioralProfile} (independent : graph.ReadyIndependent profile)
    (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right) (leftOwner rightOwner : Player)
    (leftActor : graph.actor? left = some leftOwner)
    (rightActor : graph.actor? right = some rightOwner) :
    (policyStepThen profile config left right leftReady rightReady different
      leftOwner rightOwner leftActor rightActor).map (storeRecall graph) =
    (policyStepThen profile config right left rightReady leftReady different.symm
      rightOwner leftOwner rightActor leftActor).map (storeRecall graph) := by
  have ownerNe : leftOwner ≠ rightOwner := by
    obtain ⟨leftOwner', rightOwner', leftActor', rightActor', ownersNe⟩ :=
      independent.ready_pair_actors leftReady rightReady different
    rw [leftActor] at leftActor'
    rw [rightActor] at rightActor'
    rw [Option.some.inj leftActor', Option.some.inj rightActor']
    exact ownersNe
  have actorsDiffer : ∀ who, graph.actor? left = some who → graph.actor? right ≠ some who := by
    intro who leftOwned rightOwned
    rw [leftActor] at leftOwned
    rw [rightActor] at rightOwned
    exact ownerNe ((Option.some.inj leftOwned).trans (Option.some.inj rightOwned).symm)
  rw [independent.policyStepThen_eq_independent config left right leftReady rightReady
      different leftOwner rightOwner leftActor rightActor ownerNe,
    independent.policyStepThen_eq_independent config right left rightReady leftReady
      different.symm rightOwner leftOwner rightActor leftActor ownerNe.symm]
  simp only [PMF.map_bind]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro rightAction _
  apply bind_congr_on_support _
  intro leftAction _
  exact stepThen_map_storeRecall_comm config left right leftReady rightReady
    different actorsDiffer leftAction rightAction

end Vegas.EventGraph
