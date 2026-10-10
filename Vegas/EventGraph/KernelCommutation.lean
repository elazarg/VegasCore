/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.CommutationRecall
import Vegas.EventGraph.Semantics

/-! # Commutation of independent event action kernels

Configuration-dependent action laws are lifted through the existing graph
executor. Stability for supported actions and intermediate configurations reduces
the two-step law to independent actions at the original configuration. Chance
sampling remains in the node evaluator, so this interface applies to chance
and strategic events without changing their semantics.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Execute two ready events with their action laws evaluated at the actual
configuration preceding each event. -/
def kernelStepThen (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second)
    (firstKernel : graph.Config → PMF (graph.Action first))
    (secondKernel : graph.Config → PMF (graph.Action second)) : PMF graph.Config :=
  (firstKernel config).bind fun firstAction =>
    (config.step first firstReady firstAction).bindOnSupport fun afterFirst member =>
      (secondKernel afterFirst).bind fun secondAction =>
        afterFirst.step second (by
          rw [config.step_cut first firstReady firstAction afterFirst member]
          exact secondReady.after_complete firstReady different.symm) secondAction

/-- Stability for the first event's supported actions and actual output
support permits both action laws to be evaluated at the original configuration. -/
theorem kernelStepThen_eq_independent
    (config : graph.Config) (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second)
    (firstKernel : graph.Config → PMF (graph.Action first))
    (secondKernel : graph.Config → PMF (graph.Action second))
    (stable : ∀ action ∈ (firstKernel config).support,
      ∀ after, after ∈ (config.step first firstReady action).support →
      secondKernel after = secondKernel config) :
    kernelStepThen config first second firstReady secondReady different
        firstKernel secondKernel =
      (firstKernel config).bind fun firstAction =>
        (secondKernel config).bind fun secondAction =>
          stepThen config first second firstReady secondReady different
            firstAction secondAction := by
  unfold kernelStepThen
  apply bind_congr_on_support _
  intro firstAction actionSupported
  let secondLaw := secondKernel config
  calc
    (config.step first firstReady firstAction).bindOnSupport
        (fun afterFirst member =>
          (secondKernel afterFirst).bind fun secondAction =>
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
        exact congrArg (fun law => law.bind fun secondAction =>
          afterFirst.step second (by
            rw [config.step_cut first firstReady firstAction afterFirst member]
            exact secondReady.after_complete firstReady different.symm) secondAction)
          (stable firstAction actionSupported afterFirst member)
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

/-- Independent event action kernels commute on the typed store. Neither
actor ownership nor the absence of chance events is required. -/
theorem kernelStepThen_map_store_comm
    (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (leftKernel : graph.Config → PMF (graph.Action left))
    (rightKernel : graph.Config → PMF (graph.Action right))
    (rightStable : ∀ action ∈ (leftKernel config).support,
      ∀ after, after ∈ (config.step left leftReady action).support →
      rightKernel after = rightKernel config)
    (leftStable : ∀ action ∈ (rightKernel config).support,
      ∀ after, after ∈ (config.step right rightReady action).support →
      leftKernel after = leftKernel config) :
    (kernelStepThen config left right leftReady rightReady different
      leftKernel rightKernel).map Config.store =
    (kernelStepThen config right left rightReady leftReady different.symm
      rightKernel leftKernel).map Config.store := by
  rw [kernelStepThen_eq_independent config left right leftReady rightReady different
      leftKernel rightKernel rightStable,
    kernelStepThen_eq_independent config right left rightReady leftReady different.symm
      rightKernel leftKernel leftStable]
  simp only [PMF.map_bind]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro rightAction _
  apply bind_congr_on_support _
  intro leftAction _
  exact stepThen_map_store_comm config left right leftReady rightReady
    different leftAction rightAction

variable [DecidableEq Player]

/-- Independent action kernels also preserve original-action recall when no
player owns both events. Events without actors satisfy this condition. -/
theorem kernelStepThen_map_storeRecall_comm
    (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (leftKernel : graph.Config → PMF (graph.Action left))
    (rightKernel : graph.Config → PMF (graph.Action right))
    (rightStable : ∀ action ∈ (leftKernel config).support,
      ∀ after, after ∈ (config.step left leftReady action).support →
      rightKernel after = rightKernel config)
    (leftStable : ∀ action ∈ (rightKernel config).support,
      ∀ after, after ∈ (config.step right rightReady action).support →
      leftKernel after = leftKernel config)
    (actorsDiffer : ∀ who, graph.actor? left = some who → graph.actor? right ≠ some who) :
    (kernelStepThen config left right leftReady rightReady different
      leftKernel rightKernel).map (storeRecall graph) =
    (kernelStepThen config right left rightReady leftReady different.symm
      rightKernel leftKernel).map (storeRecall graph) := by
  rw [kernelStepThen_eq_independent config left right leftReady rightReady different
      leftKernel rightKernel rightStable,
    kernelStepThen_eq_independent config right left rightReady leftReady different.symm
      rightKernel leftKernel leftStable]
  simp only [PMF.map_bind]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro rightAction _
  apply bind_congr_on_support _
  intro leftAction _
  exact stepThen_map_storeRecall_comm config left right leftReady rightReady
    different actorsDiffer leftAction rightAction

/-- Two ownerless sampling events commute on both the store and every
player's recall. Their retained distribution code supplies all randomness. -/
theorem chanceStepThen_map_storeRecall_comm
    (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (leftChance : graph.actor? left = none) (rightChance : graph.actor? right = none) :
    (kernelStepThen config left right leftReady rightReady different
      (fun _ => PMF.pure ((graph.nodes left).actionOfActorNone leftChance))
      (fun _ => PMF.pure ((graph.nodes right).actionOfActorNone rightChance))).map
        (storeRecall graph) =
    (kernelStepThen config right left rightReady leftReady different.symm
      (fun _ => PMF.pure ((graph.nodes right).actionOfActorNone rightChance))
      (fun _ => PMF.pure ((graph.nodes left).actionOfActorNone leftChance))).map
        (storeRecall graph) := by
  apply kernelStepThen_map_storeRecall_comm
  · intro _ _ _ _
    rfl
  · intro _ _ _ _
    rfl
  · intro who owned
    rw [leftChance] at owned
    cases owned

end Vegas.EventGraph
