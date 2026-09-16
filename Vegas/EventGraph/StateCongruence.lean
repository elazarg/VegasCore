/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.PolicyCommutation
import Vegas.EventGraph.CanonicalStep

/-! # Semantic-state congruence for normalized graph execution -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Execution state relevant to normalized policies and terminal store readout.
Chronological completion metadata is deliberately absent. -/
def SemanticKey (graph : Vegas.EventGraph Player L) :=
  graph.order.Cut ×
    (Store graph.layout × (Player → List graph.Completion))

def semanticKey (graph : Vegas.EventGraph Player L) (config : graph.Config) :
    graph.SemanticKey :=
  (config.cut, graph.storeRecall config)

theorem semanticKey_cut_eq {left right : graph.Config}
    (same : graph.semanticKey left = graph.semanticKey right) :
    left.cut = right.cut := congrArg Prod.fst same

theorem semanticKey_store_eq {left right : graph.Config}
    (same : graph.semanticKey left = graph.semanticKey right) :
    left.store = right.store := congrArg (fun key => key.2.1) same

theorem semanticKey_ownCompletions_eq {left right : graph.Config}
    (same : graph.semanticKey left = graph.semanticKey right) (who : Player) :
    graph.ownCompletions who left.history =
      graph.ownCompletions who right.history :=
  congrFun (congrArg (fun key => key.2.2) same) who

/-- Normalization erases precisely the chronological component missing from
`semanticKey`; equal keys therefore give equal normalized observations. -/
theorem normalizeObservation_congr_of_semanticKey_eq
    {left right : graph.Config} (same : graph.semanticKey left = graph.semanticKey right)
    (event : graph.EventId) (who : Player) :
    graph.normalizeObservation event who (graph.playerObserve who left) =
      graph.normalizeObservation event who (graph.playerObserve who right) := by
  apply PlayerObservation.ext graph
  · rfl
  · apply graph.playerStore_congr
    intro field _
    exact congrFun (semanticKey_store_eq same) field
  · exact semanticKey_ownCompletions_eq same who

/-- Execute one fixed ready event using the normalized profile. Chance nodes
retain their ordinary evaluator law and unique unit action. -/
def normalizedPolicyStep (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) : FinDist graph.Config :=
  match actor : graph.actor? event with
  | some who =>
      (graph.normalizePolicy who (profile who) event actor
        (graph.playerObserve who config)).bind (config.step event ready)
  | none => config.step event ready
      (EventCode.actionOfActorNone (graph.nodes event) actor)

/-- Completing the same event with the same action and value preserves key
equality. Readiness witnesses are proof irrelevant. -/
theorem semanticKey_complete_congr {left right : graph.Config}
    (same : graph.semanticKey left = graph.semanticKey right)
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    graph.semanticKey (left.complete event leftReady action value) =
      graph.semanticKey (right.complete event rightReady action value) := by
  have cutEq := semanticKey_cut_eq same
  have storeEq := semanticKey_store_eq same
  have recallEq := fun who => semanticKey_ownCompletions_eq same who
  change
    ((left.complete event leftReady action value).cut,
      (left.complete event leftReady action value).store,
      fun who => graph.ownCompletions who
        (left.complete event leftReady action value).history) =
    ((right.complete event rightReady action value).cut,
      (right.complete event rightReady action value).store,
      fun who => graph.ownCompletions who
        (right.complete event rightReady action value).history)
  apply Prod.ext
  · change left.cut.complete event leftReady = right.cut.complete event rightReady
    apply EventOrder.Cut.ext
    apply Finset.ext
    intro query
    simp [cutEq]
  · apply Prod.ext
    · rw [store_complete, store_complete, storeEq]
    · funext who
      simp only [Config.complete_history, ownCompletions,
        List.filter_append, List.filter_cons, List.filter_nil]
      congr 1
      exact recallEq who

/-- For a fixed action, one ordinary event step has the same semantic-key law
from equal semantic states. -/
theorem step_map_semanticKey_congr {left right : graph.Config}
    (same : graph.semanticKey left = graph.semanticKey right)
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event) (action : graph.Action event) :
    (left.step event leftReady action).map graph.semanticKey =
      (right.step event rightReady action).map graph.semanticKey := by
  have evalEq : (graph.nodes event).eval? action left.store =
      (graph.nodes event).eval? action right.store := by
    apply EventCode.eval?_congr
    intro field _
    exact congrFun (semanticKey_store_eq same) field
  cases found : (graph.nodes event).eval? action left.store with
  | none =>
      have present := EventCode.eval?_isSome_of_reads (graph.nodes event) action left.store
        (fun _ read => left.read_available leftReady read)
      simp [found] at present
  | some law =>
    have rightFound : (graph.nodes event).eval? action right.store = some law :=
      evalEq ▸ found
    rw [left.step_eq_map_of_eval event leftReady action law found,
      right.step_eq_map_of_eval event rightReady action law rightFound]
    simp only [FinDist.map_comp]
    apply FinDist.map_congr_of_eq_on_support
    intro value _
    exact semanticKey_complete_congr same event leftReady rightReady action value

/-- The normalized one-event kernel factors through `semanticKey`. -/
theorem normalizedPolicyStep_map_semanticKey_congr
    (profile : graph.BehavioralProfile) {left right : graph.Config}
    (same : graph.semanticKey left = graph.semanticKey right)
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event) :
    (graph.normalizedPolicyStep profile left event leftReady).map graph.semanticKey =
      (graph.normalizedPolicyStep profile right event rightReady).map graph.semanticKey := by
  unfold normalizedPolicyStep
  split
  · rename_i who actor
    have observationEq := normalizeObservation_congr_of_semanticKey_eq same event who
    have actionLaw :
        graph.normalizePolicy who (profile who) event actor
            (graph.playerObserve who left) =
          graph.normalizePolicy who (profile who) event actor
            (graph.playerObserve who right) := by
      exact congrArg (profile who event actor) observationEq
    rw [actionLaw, FinDist.map_bind, FinDist.map_bind]
    apply FinDist.bind_congr
    intro action _
    exact step_map_semanticKey_congr same event leftReady rightReady action
  · exact step_map_semanticKey_congr same event leftReady rightReady _

/-- A supported normalized policy step completes exactly the selected event. -/
theorem normalizedPolicyStep_cut
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (next : graph.Config)
    (member : next ∈ (graph.normalizedPolicyStep profile config event ready).support) :
    next.cut = config.cut.complete event ready := by
  unfold normalizedPolicyStep at member
  split at member
  · rw [FinDist.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨action, _, stepMember⟩ := member
    exact config.step_cut event ready action next stepMember
  · exact config.step_cut event ready _ next member

/-- Every supported normalized policy step completes exactly one previously
unfinished event. -/
theorem normalizedPolicyStep_remaining
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (next : graph.Config)
    (member : next ∈ (graph.normalizedPolicyStep profile config event ready).support) :
    next.remaining + 1 = config.remaining := by
  unfold normalizedPolicyStep at member
  split at member
  · rw [FinDist.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨action, _, stepMember⟩ := member
    exact config.remaining_step event ready action next stepMember
  · exact config.remaining_step event ready _ next member

/-- Expose one canonical-runner step as the generic normalized fixed-event
kernel. The event need only be ready and least among unfinished events. -/
theorem runPlan_canonical_normalized_step
    (profile : graph.BehavioralProfile) (fuel : Nat) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val) :
    graph.runPlan
        (graph.policyPlan (graph.normalizeProfile profile) graph.canonicalScheduler)
        (fuel + 1) config =
      (graph.normalizedPolicyStep profile config event ready).bind
        (graph.runPlan
          (graph.policyPlan (graph.normalizeProfile profile) graph.canonicalScheduler)
          fuel) := by
  unfold normalizedPolicyStep
  split
  · rename_i who actor
    simpa [normalizeProfile, normalizePolicy, FinDist.bind_bind] using
      graph.runPlan_canonical_actor (graph.normalizeProfile profile) fuel config
        event ready least who actor
  · rename_i ownerless
    simpa [FinDist.bind_bind] using
      graph.runPlan_canonical_ownerless (graph.normalizeProfile profile) fuel config
        event ready least ownerless

/-- Compose equal semantic-state laws with continuations that depend only on
the semantic key. This is the finite-law quotient step used after a local
diamond. -/
theorem bind_eq_of_semanticKey_map_eq
    (left right : FinDist graph.Config)
    (same : left.map graph.semanticKey = right.map graph.semanticKey)
    (leftNext rightNext : graph.Config → FinDist graph.SemanticKey)
    (congruent : ∀ leftConfig ∈ left.support, ∀ rightConfig ∈ right.support,
      graph.semanticKey leftConfig = graph.semanticKey rightConfig →
        leftNext leftConfig = rightNext rightConfig) :
    left.bind leftNext = right.bind rightNext :=
  FinDist.bind_eq_of_map_eq left right graph.semanticKey graph.semanticKey same
    leftNext rightNext congruent

omit [DecidableEq Player] in
private theorem EventCode.output_public_of_actor_none
    {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (ownerless : code.actor = none) :
    output.IsPublic := by
  cases code <;> simp_all [EventCode.actor, EventField.IsPublic]

/-- Distinct simultaneously ready events in a public-barrier graph are both
strategic, have owners, and those owners differ. A public chance/resolution
event is comparable with every other event and therefore cannot coexist. -/
theorem BarrierOrdered.ready_pair_actors
    (ordered : graph.BarrierOrdered) {config : graph.Config}
    {left right : graph.EventId} (leftReady : config.cut.Ready left)
    (rightReady : config.cut.Ready right) (different : left ≠ right) :
    ∃ leftOwner rightOwner,
      graph.actor? left = some leftOwner ∧
      graph.actor? right = some rightOwner ∧ leftOwner ≠ rightOwner := by
  have strategic (event other : graph.EventId) (eventReady : config.cut.Ready event)
      (otherReady : config.cut.Ready other) (different : event ≠ other) :
      ∃ owner, graph.actor? event = some owner := by
    cases actor : graph.actor? event with
    | some owner => exact ⟨owner, rfl⟩
    | none =>
        have isPublic := EventCode.output_public_of_actor_none
          (graph.nodes event) (by simpa [EventGraph.actor?] using actor)
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne different) with before | after
        · have predecessor : event ∈ graph.order.predecessors other := by
            exact ordered other
              (barrierOrder_public_prior graph.outputLayout before isPublic)
          exact False.elim (eventReady.1 (otherReady.2 predecessor))
        · have predecessor : other ∈ graph.order.predecessors event := by
            exact ordered event
              (barrierOrder_public_event graph.outputLayout after isPublic)
          exact False.elim (otherReady.1 (eventReady.2 predecessor))
  obtain ⟨leftOwner, leftActor⟩ := strategic left right leftReady rightReady different
  obtain ⟨rightOwner, rightActor⟩ :=
    strategic right left rightReady leftReady different.symm
  exact ⟨leftOwner, rightOwner, leftActor, rightActor,
    ordered.informationDiscipline.ready_actor_ne leftReady rightReady different
      leftActor rightActor⟩

/-- Every result of the two-event policy kernel has the deterministic cut
obtained by completing the two selected events. -/
theorem policyStepThen_result_cut
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (first second : graph.EventId)
    (firstReady : config.cut.Ready first) (secondReady : config.cut.Ready second)
    (different : first ≠ second) (firstOwner secondOwner : Player)
    (firstActor : graph.actor? first = some firstOwner)
    (secondActor : graph.actor? second = some secondOwner)
    (result : graph.Config)
    (member : result ∈ (policyStepThen profile config first second firstReady secondReady
      different firstOwner secondOwner firstActor secondActor).support) :
    result.cut = (config.cut.complete first firstReady).complete second
      (secondReady.after_complete firstReady different.symm) := by
  unfold policyStepThen at member
  rw [FinDist.support_bind] at member
  simp only [Set.mem_iUnion] at member
  obtain ⟨firstAction, _, afterAction⟩ := member
  rw [FinDist.support_bindOnSupport] at afterAction
  simp only [Set.mem_iUnion] at afterAction
  obtain ⟨afterFirst, firstMember, afterFirstLaw⟩ := afterAction
  rw [FinDist.support_bind] at afterFirstLaw
  simp only [Set.mem_iUnion] at afterFirstLaw
  obtain ⟨secondAction, _, secondMember⟩ := afterFirstLaw
  have resultCut := Config.step_cut afterFirst second _ secondAction result secondMember
  have firstCut := Config.step_cut config first firstReady firstAction afterFirst firstMember
  apply EventOrder.Cut.ext
  apply Finset.ext
  intro query
  have resultCompleted := congrArg EventOrder.Cut.completed resultCut
  rw [resultCompleted]
  simp [firstCut]

/-- The normalized two-event diamond preserves the complete semantic key, not
only its store/recall component. -/
theorem BarrierOrdered.policyStepThen_map_semanticKey_comm
    (ordered : graph.BarrierOrdered) (profile : graph.BehavioralProfile)
    (config : graph.Config) (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right) (leftOwner rightOwner : Player)
    (leftActor : graph.actor? left = some leftOwner)
    (rightActor : graph.actor? right = some rightOwner) :
    (policyStepThen profile config left right leftReady rightReady different
      leftOwner rightOwner leftActor rightActor).map graph.semanticKey =
    (policyStepThen profile config right left rightReady leftReady different.symm
      rightOwner leftOwner rightActor leftActor).map graph.semanticKey := by
  let leftLaw := policyStepThen profile config left right leftReady rightReady different
    leftOwner rightOwner leftActor rightActor
  let rightLaw := policyStepThen profile config right left rightReady leftReady
    different.symm rightOwner leftOwner rightActor leftActor
  have recall := ordered.policyStepThen_map_storeRecall_comm profile config left right
    leftReady rightReady different leftOwner rightOwner leftActor rightActor
  have leftRewrite : leftLaw.map graph.semanticKey =
      (leftLaw.map (storeRecall graph)).map
        (fun recalled =>
          ((config.cut.complete left leftReady).complete right
            (rightReady.after_complete leftReady different.symm), recalled)) := by
    rw [FinDist.map_comp]
    apply FinDist.map_congr_of_eq_on_support
    intro result member
    apply Prod.ext
    · change result.cut = _
      exact policyStepThen_result_cut profile config left right leftReady rightReady
        different leftOwner rightOwner leftActor rightActor result member
    · rfl
  have rightRewrite : rightLaw.map graph.semanticKey =
      (rightLaw.map (storeRecall graph)).map
        (fun recalled =>
          ((config.cut.complete left leftReady).complete right
            (rightReady.after_complete leftReady different.symm), recalled)) := by
    rw [FinDist.map_comp]
    apply FinDist.map_congr_of_eq_on_support
    intro result member
    apply Prod.ext
    · change result.cut = _
      rw [policyStepThen_result_cut profile config right left rightReady leftReady
        different.symm rightOwner leftOwner rightActor leftActor result member]
      exact config.cut.complete_comm rightReady leftReady different.symm
    · rfl
  rw [leftRewrite, rightRewrite, recall]

end Vegas.EventGraph
