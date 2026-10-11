/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnilateralFrontier
import Vegas.Pending.ReactiveDeviationInclusion

/-! # Native accepted focal calls advance mixed source frontiers -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Actual accepted envelopes of the arbitrary focal player advance the
reachable mixed source frontier with the native handler's action and output.
Only foreign players need genuine prescribed posterior support. -/
theorem ReactiveUnilateralFrontier.include_focal (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (focal : Player) (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal control.execution memories frontier)
    (consistent : ∀ owner, owner ≠ focal →
      (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (control.execution.recall owner))
    (supported : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (message : Message Player (WitnessedPacket graph))
    (named : message.payload.call.event? graph = some event) (after : State graph)
    (found : control.execution.network.lookup message.id = some message)
    (accepted : (runtime.reactiveApplication leaks).handle control.execution.application message =
      some after) :
    ∃ (ready : frontier.cut.Ready event) (action : graph.Action event) (final : graph.Config),
      final ∈ (frontier.step event ready action).support ∧
      runtime.ReactiveUnilateralFrontier leaks focal
        (control.execution.includePending (runtime.reactiveApplication leaks) message.id)
        memories final := by
  obtain ⟨physicalReady, action, physicalSupported, sourceHistory⟩ :=
    runtime.originalConfig_include_focal_history leaks inputs horizon scheduler control trace
      memories focal related.empty event actor message named after found accepted
  have domain : ∀ query, query ∈ frontier.cut.completed ↔
      query ∈ control.execution.application.config.cut.completed ∨
        ∃ owner, owner ≠ focal ∧ ∃ remembered,
          some remembered ∈ memories owner ∧ remembered.event = query := by
    intro query
    rw [related.domain query]
    constructor
    · rintro (physical | ⟨owner, remembered, member, named⟩)
      · exact Or.inl physical
      · refine Or.inr ⟨owner, ?_, remembered, member, named⟩
        intro same
        subst owner
        simp [related.empty] at member
    · rintro (physical | ⟨owner, _, remembered, member, named⟩)
      · exact Or.inl physical
      · exact Or.inr ⟨owner, remembered, member, named⟩
  obtain ⟨frontierReady, joint, first, second, common⟩ :=
    runtime.unilateralFrontier_coupled_step leaks profile control.execution focal memories
      consistent supported frontier domain related.settled related.inputs.symm event actor
        physicalReady action
  have afterSupport : after.config ∈ (joint.map Prod.fst).support := by
    rw [first]
    exact physicalSupported
  obtain ⟨pair, pairSupported, pairFirst⟩ := PMF.support_map .. ▸ afterSupport
  have finalSupported : pair.2 ∈ (frontier.step event frontierReady action).support := by
    rw [← second, PMF.support_map]
    exact ⟨pair, pairSupported, rfl⟩
  obtain ⟨settled, sameInputs⟩ := common pair pairSupported
  let next := control.execution.includePending (runtime.reactiveApplication leaks) message.id
  have included : next.application.config = after.config := by
    simp only [next, ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, accepted, Option.getD_some]
  have pairEq : next.application.config = pair.1 := included.trans pairFirst.symm
  refine ⟨frontierReady, action, pair.2, finalSupported, ?_⟩
  apply ReactiveUnilateralFrontier.step_focal runtime leaks focal control.execution next
    memories frontier pair.2 related event actor physicalReady frontierReady action
  · rw [included]
    exact physicalSupported
  · exact finalSupported
  · rw [pairEq]
    exact settled
  · rw [pairEq]
    exact sameInputs
  · exact sourceHistory

end Vegas.EventGraphRuntime
