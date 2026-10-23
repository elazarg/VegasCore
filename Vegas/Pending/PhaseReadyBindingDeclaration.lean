/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseReceiptOrder
import Vegas.Pending.CompletedBindingReadback
import Vegas.Pending.PhaseCompletedBindingMeaning
import Vegas.Pending.ReactiveBindingFrameStep

/-! # Actual earlier declarations at a surviving owner's ready binding -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

/-- Readiness and survival derive an earlier owned binding's accepted handle
and its exact typed store cell, even after other owners have failed. -/
theorem phase_ready_earlier_binding_read
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (ordered : graph.RevealRelaxedOrdered)
    (phase : RuntimePhase graph)
    (installed : control.execution.application.phases.head? = some phase)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (active : owner ∉ control.execution.application.current.excluded)
    (earlier : graph.EventId) (priorPayload : L.Ty)
    (priorBinding : graph.outputLayout earlier = .binding owner priorPayload)
    (inside : earlier ∈ phase.events) (before : earlier.val < event.val) :
    ∃ candidate : Handle graph, candidate.1 = owner ∧
      control.execution.application.current.native.accepted (.inr earlier) = some candidate ∧
      (⟨.inr earlier, priorBinding⟩ : FieldRef graph.layout (.binding owner priorPayload)).get?
          control.execution.application.current.native.config.store =
        some (control.execution.application.current.native.bindingResult candidate priorPayload) :=
    by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have exclusions := phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler raw
  have receipts := (exclusions.installed phase installed).ready_binding_receipts ordered event
    ready owner payload binding active
  have present := receipts.2 earlier ((phase.mem_events earlier).mp inside).1 before
    priorPayload priorBinding
  obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
  have records :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  obtain ⟨_otherPayload, typed⟩ := records.accepted_typed (.inr earlier) candidate accepted
  have owned : candidate.1 = owner :=
    (EventField.binding.inj (typed.symm.trans priorBinding)).1
  have dependency : earlier ∈ graph.order.predecessors event :=
    ordered.keeps (barrierOrder_same_owner graph.outputLayout before (by
      rw [priorBinding, binding]
      rfl)) (Or.inl (by simp only [priorBinding, EventField.IsPublication, not_false_eq_true]))
  have read := records.binding_read
    (⟨.inr earlier, priorBinding⟩ : FieldRef graph.layout (.binding owner priorPayload))
      earlier rfl (ready.2 dependency)
  exact ⟨candidate, owned, accepted, by simpa only [accepted, Option.elim_some] using read⟩

end Vegas.EventGraphRuntime
