/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCandidateBudget
import Vegas.Pending.ReactiveAssociationEvidence
import Vegas.Pending.ReactiveBindingAllocation
import Interaction.ReactiveAllocation
import Vegas.Pending.ReactivePolicyFacts

/-! # Binding resources at actual native decisions

A legal active history has a fresh, unused candidate below the interaction
horizon. A ready event has no accepted handle. These facts hold after arbitrary
earlier responses, independently of a source profile or equilibrium.

At a clean allocation prefix the same candidate is selected by the public
binding count. Thus finite handle capacity can be fixed from the interaction
bound; source compilation need not assume a fresh resource at each decision.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveBinding_resources_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : graph.EventId) (ready : control.execution.application.config.cut.Ready event) :
    ∃ serial, serial < horizon ∧
      reactiveFreshSlot
        (control.execution.observe (runtime.reactiveApplication leaks) who).application =
          some serial ∧
      control.execution.application.candidates.lookup (who, .prepared serial) = .fresh ∧
      control.execution.application.HandleUnused (who, .prepared serial) ∧
      control.execution.application.accepted (.inr event) = none ∧
      control.execution.network.SerialsBeforeNext := by
  obtain ⟨serial, bounded, selected⟩ := runtime.reactiveFreshSlot_lt_horizon leaks inputs horizon
    scheduler control trace who active
  have valid := runtime.reactiveBindingInvariant_history leaks inputs horizon scheduler trace
  have fresh := reactiveFreshSlot_spec
    (control.execution.observe (runtime.reactiveApplication leaks) who).application serial selected
  have unused : control.execution.application.HandleUnused (who, .prepared serial) :=
    fun field associated => valid.accepted_fixed field _ associated fresh
  refine ⟨serial, bounded, selected, fresh, unused, ?_,
    (runtime.reactiveApplication leaks).serialsBeforeNext_history scheduler
      (inputs.map State.initial) horizon trace⟩
  cases associated : control.execution.application.accepted (.inr event) with
  | none => rfl
  | some candidate =>
      exact False.elim (ready.1
        (valid.toAssociationInvariant.accepted_complete event candidate associated))

/-- The publicly determined canonical serial fits the finite native capacity
whenever that capacity covers the interaction horizon. -/
theorem preparedPrefix_binding_resources (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon capacity : Nat)
    (enough : horizon ≤ capacity)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : graph.EventId) (ready : control.execution.application.config.cut.Ready event)
    (allocated : control.execution.application.PreparedPrefix who) :
    let serial := control.execution.application.publicView.bindingCount who
    serial < capacity ∧
      reactiveFreshSlot
        (control.execution.observe (runtime.reactiveApplication leaks) who).application =
          some serial ∧
      control.execution.application.candidates.lookup (who, .prepared serial) = .fresh ∧
      control.execution.application.HandleUnused (who, .prepared serial) ∧
      control.execution.application.accepted (.inr event) = none ∧
      control.execution.network.SerialsBeforeNext := by
  obtain ⟨serial, bounded, selected, fresh, unused, vacant, serials⟩ :=
    runtime.reactiveBinding_resources_history leaks inputs horizon scheduler control trace who
      active event ready
  have canonical := allocated.freshSlot runtime leaks
  have same : serial = control.execution.application.publicView.bindingCount who :=
    Option.some.inj (selected.symm.trans canonical)
  simpa only [← same] using
    And.intro (lt_of_lt_of_le bounded enough) ⟨selected, fresh, unused, vacant, serials⟩

/-- Every active ready binding decision transmits, including sampled failure.
Actual horizon resources rule out silence from an exhausted candidate lookup. -/
theorem reactiveDecision_binding_transmits_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (event : graph.EventId) (ready : control.execution.application.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (action : graph.Action event) :
    ∃ serial material, serial < horizon ∧
      (runtime.reactiveDecision leaks who event action
        (control.execution.observe
          (runtime.reactiveApplication leaks) who).application).transmission =
          some material ∧ material.call.packet = .commitment event (who, .prepared serial) := by
  obtain ⟨serial, bounded, selected, _⟩ := runtime.reactiveBinding_resources_history leaks inputs
    horizon scheduler control trace who active event ready
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (who, .prepared serial),
      match (cast (congrArg EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  refine ⟨serial, material, bounded, ?_, rfl⟩
  simp only [reactiveDecision, node, selected, Option.map_some, material]
  rfl

end Vegas.EventGraphRuntime
