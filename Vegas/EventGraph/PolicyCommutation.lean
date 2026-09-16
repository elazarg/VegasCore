/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.CommutationRecall
import Vegas.EventGraph.NormalizedPolicy

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
    (secondActor : graph.actor? second = some secondOwner) : FinDist graph.Config :=
  (graph.normalizePolicy firstOwner (profile firstOwner) first firstActor
      (graph.playerObserve firstOwner config)).bind fun firstAction =>
    (config.step first firstReady firstAction).bindOnSupport fun afterFirst member =>
      (graph.normalizePolicy secondOwner (profile secondOwner) second secondActor
          (graph.playerObserve secondOwner afterFirst)).bind fun secondAction =>
        afterFirst.step second (by
          rw [config.step_cut first firstReady firstAction afterFirst member]
          exact secondReady.after_complete firstReady different.symm) secondAction

/-- When the two owners differ, the second normalized kernel can be pulled
back across the first actual step.  The resulting law draws both actions from
the common pre-step information and then uses the fixed-action `stepThen`.
-/
theorem BarrierOrdered.policyStepThen_eq_independent
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
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
  apply FinDist.bind_congr
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
        apply FinDist.bindOnSupport_congr
        intro afterFirst member
        rw [Config.step, FinDist.support_map] at member
        obtain ⟨value, _, rfl⟩ := member
        have stable := (ordered.normalizePolicy_complete_foreign
          (profile secondOwner) config second first secondReady firstReady secondActor
          firstOwner firstActor differentOwner firstAction value).2
        exact congrArg (fun law => law.bind fun secondAction =>
          (config.complete first firstReady firstAction value).step second
            (secondReady.after_complete firstReady different.symm) secondAction) stable
    _ = secondLaw.bind fun secondAction =>
        (config.step first firstReady firstAction).bindOnSupport fun afterFirst member =>
          afterFirst.step second (by
            rw [config.step_cut first firstReady firstAction afterFirst member]
            exact secondReady.after_complete firstReady different.symm) secondAction := by
      exact (FinDist.bind_bindOnSupport_comm secondLaw
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
theorem BarrierOrdered.policyStepThen_map_storeRecall_comm
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right) (leftOwner rightOwner : Player)
    (leftActor : graph.actor? left = some leftOwner)
    (rightActor : graph.actor? right = some rightOwner) :
    (policyStepThen profile config left right leftReady rightReady different
      leftOwner rightOwner leftActor rightActor).map (storeRecall graph) =
    (policyStepThen profile config right left rightReady leftReady different.symm
      rightOwner leftOwner rightActor leftActor).map (storeRecall graph) := by
  have discipline := ordered.informationDiscipline
  have ownerNe : leftOwner ≠ rightOwner :=
    discipline.ready_actor_ne leftReady rightReady different leftActor rightActor
  rw [ordered.policyStepThen_eq_independent profile config left right leftReady rightReady
      different leftOwner rightOwner leftActor rightActor ownerNe,
    ordered.policyStepThen_eq_independent profile config right left rightReady leftReady
      different.symm rightOwner leftOwner rightActor leftActor ownerNe.symm]
  simp only [FinDist.map_bind]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro rightAction _
  apply FinDist.bind_congr
  intro leftAction _
  exact stepThen_map_storeRecall_comm discipline config left right leftReady rightReady
    different leftAction rightAction

end Vegas.EventGraph
