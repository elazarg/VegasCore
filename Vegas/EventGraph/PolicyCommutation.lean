/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.KernelCommutation
import Vegas.EventGraph.NormalizedPolicy
import Vegas.EventGraph.RevealRelaxation

/-! # Local commutation of normalized behavioral kernels

This module lifts the fixed-action event diamond to the two actual behavioral
kernels at simultaneously ready events.  It composes ordinary
`Config.step` calls and does not define another graph executor.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The actual action kernel at a fixed event. Ownerless events have their
unique action; their random output remains in the original node evaluator. -/
def normalizedAction (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) : PMF (graph.Action event) :=
  match actor : graph.actor? event with
  | some who => graph.normalizePolicy who (profile who) event actor
      (graph.playerObserve who config)
  | none => PMF.pure (EventCode.actionOfActorNone (graph.nodes event) actor)

theorem normalizedAction_of_actor (profile : graph.BehavioralProfile)
    (config : graph.Config) (event : graph.EventId) (who : Player)
    (actor : graph.actor? event = some who) :
    normalizedAction profile config event =
      graph.normalizePolicy who (profile who) event actor (graph.playerObserve who config) := by
  unfold normalizedAction
  split
  · rename_i actual actualActor
    have same : actual = who := Option.some.inj (actualActor.symm.trans actor)
    subst actual
    rfl
  · rename_i ownerless
    rw [ownerless] at actor
    cases actor

theorem normalizedAction_of_ownerless (profile : graph.BehavioralProfile)
    (config : graph.Config) (event : graph.EventId) (ownerless : graph.actor? event = none) :
    normalizedAction profile config event =
      PMF.pure (EventCode.actionOfActorNone (graph.nodes event) ownerless) := by
  unfold normalizedAction
  split
  · rename_i who actor
    rw [ownerless] at actor
    cases actor
  · rfl

/-- Execute one fixed ready event using the normalized profile. Chance nodes
retain their ordinary evaluator law and unique unit action. -/
def normalizedPolicyStep (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) : PMF graph.Config :=
  match actor : graph.actor? event with
  | some who =>
      (graph.normalizePolicy who (profile who) event actor
        (graph.playerObserve who config)).bind (config.step event ready)
  | none => config.step event ready
      (EventCode.actionOfActorNone (graph.nodes event) actor)

theorem normalizedPolicyStep_eq_bind (profile : graph.BehavioralProfile)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event) :
    graph.normalizedPolicyStep profile config event ready =
      (normalizedAction profile config event).bind (config.step event ready) := by
  unfold normalizedPolicyStep normalizedAction
  split
  · rfl
  · exact (PMF.pure_bind _ _).symm

/-- Run two ready events, evaluating their actual normalized action kernels at
the configuration preceding each event, including ownerless sampling events. -/
def policyStepThen (profile : graph.BehavioralProfile) (config : graph.Config)
    (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) : PMF graph.Config :=
  kernelStepThen config first second firstReady secondReady different
    (fun current => normalizedAction profile current first)
    (fun current => normalizedAction profile current second)

/-- Primitive conditions for scheduler independence. No player owns two
simultaneously ready events, and each actual normalized action law is stable
under every other ready completion. The latter includes chance outputs. -/
structure ReadyIndependent (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) : Prop where
  ready_pair_not_actor : ∀ {cut : graph.order.Cut} {left right : graph.EventId},
    cut.Ready left → cut.Ready right → left ≠ right →
      ∀ who, graph.actor? left = some who → graph.actor? right ≠ some who
  normalizedAction_complete : ∀ (config : graph.Config) (event other : graph.EventId),
    config.cut.Ready event → ∀ (otherReady : config.cut.Ready other), event ≠ other →
      ∀ (action : graph.Action other) (value : (graph.outputLayout other).Value),
        normalizedAction profile (config.complete other otherReady action value) event =
          normalizedAction profile config event

/-- A graph made entirely of chance events is ready independent for every
profile: all action laws are the same fixed unit laws. -/
theorem readyIndependent_of_ownerless (profile : graph.BehavioralProfile)
    (ownerless : ∀ event, graph.actor? event = none) : graph.ReadyIndependent profile where
  ready_pair_not_actor _ _ _ _ actor := by simp [ownerless] at actor
  normalizedAction_complete _ event _ _ _ _ _ _ := by
    rw [normalizedAction_of_ownerless _ _ _ (ownerless event),
      normalizedAction_of_ownerless _ _ _ (ownerless event)]

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
  ready_pair_not_actor leftReady rightReady different who leftActor rightActor := by
    obtain ⟨leftOwner, rightOwner, leftOwned, rightOwned, ownersNe⟩ :=
      ordered.ready_pair_actors leftReady rightReady different
    exact ownersNe ((Option.some.inj (leftOwned.symm.trans leftActor)).trans
      (Option.some.inj (rightOwned.symm.trans rightActor)).symm)
  normalizedAction_complete config event other eventReady otherReady different action value := by
    obtain ⟨who, foreign, actor, otherActor, differentOwner⟩ :=
      ordered.ready_pair_actors eventReady otherReady different
    rw [normalizedAction_of_actor _ _ _ who actor,
      normalizedAction_of_actor _ _ _ who actor]
    exact congrArg ((profile _) event actor)
      (ordered.normalizeObservation_complete_foreign config event other eventReady
        otherReady actor foreign otherActor differentOwner.symm action value).2

/-- The two sequential normalized behavioral kernels commute after projecting
to the typed store and every player's original-action recall. -/
theorem ReadyIndependent.policyStepThen_map_storeRecall_comm
    {profile : graph.BehavioralProfile} (independent : graph.ReadyIndependent profile)
    (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right) :
    (policyStepThen profile config left right leftReady rightReady different).map
        (storeRecall graph) =
      (policyStepThen profile config right left rightReady leftReady different.symm).map
        (storeRecall graph) := by
  apply kernelStepThen_map_storeRecall_comm config left right leftReady rightReady different
    (fun current => normalizedAction profile current left)
    (fun current => normalizedAction profile current right)
  · intro action _ after member
    rw [Config.step, PMF.support_map] at member
    obtain ⟨value, _, rfl⟩ := member
    exact independent.normalizedAction_complete config right left rightReady leftReady
      different.symm action value
  · intro action _ after member
    rw [Config.step, PMF.support_map] at member
    obtain ⟨value, _, rfl⟩ := member
    exact independent.normalizedAction_complete config left right leftReady rightReady
      different action value
  · exact independent.ready_pair_not_actor leftReady rightReady different

end Vegas.EventGraph
