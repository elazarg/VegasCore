/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSlotPolicy

/-! # Every bounded fresh slot is offered at actual unsent binding sites -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

/-- Actual recall, permanent candidate freshness and genuine readiness make
every bounded fresh slot legal for every typed value, across prior attempts. -/
theorem mem_phaseBindingSlots_of_history
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (bounded : serial < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh) :
    serial ∈ phaseBindingSlots runtime leaks bounds who event payload
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who) := by
  classical
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have fixed := phaseOwnCommitmentsFixed_history runtime leaks _ horizon scheduler raw
  have recalled := countRecall_history runtime leaks raw
  rw [phaseBindingSlots, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr bounded, fresh, fun result => ?_⟩
  rw [mem_onePacketActions]
  exact ⟨phaseBindingResponse_available runtime leaks bounds who _ _ event payload values
      result serial bounded, Or.inr (phaseBindingResponse_permitted runtime leaks
        control.execution recalled fixed who event payload outputEq request unsent result
          serial fresh)⟩

/-- The actual horizon bound supplies at least one eligible slot, while the
slot tier retains every other bounded fresh slot with positive uniform mass. -/
theorem phaseBindingSlots_nonempty_of_history
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (who : Player) (active : control.actor = some who)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    (phaseBindingSlots runtime leaks bounds who event payload
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who)).Nonempty := by
  have raw := menu.toRawTrace (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  obtain ⟨serial, bounded, selected⟩ := PhaseCandidates.reactiveFreshSlot_lt_horizon runtime leaks
    plan inputs horizon scheduler control raw who active
  exact ⟨serial, mem_phaseBindingSlots_of_history runtime leaks bounds menu plan inputs horizon
    scheduler control trace who event payload outputEq request unsent values serial
      (bounded.trans_le capacity) (reactiveFreshSlot_spec _ serial selected)⟩

end Vegas.EventGraphRuntime.PhaseCount
