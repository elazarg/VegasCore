/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalSubmittedBindings
import Vegas.Pending.PhaseRecordedBindingMaterial
import Vegas.Pending.PhaseBindingFreshness

/-! # Actual repaired recorded binding preparations are usable -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Persistent physical typed records plus actual counted freshness recover
the target's original preparation syntax at every remembered SEND. Canceled
logical records and retired candidate occupancy cause no exception. -/
theorem PreparedBindings.recorded_preparation_usable
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (original : (app).Execution)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (prepared : PreparedBindings runtime leaks owner original control.execution)
    (network : original.network = control.execution.network)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (entry : (app).PlayerEntry) (recorded : entry ∈ control.execution.recall owner)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩) :
    ∃ value : L.Val payload, opening.bind (fun raw => raw.as? payload) = some value := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have rawTrace := menu.toRawTrace initial horizon scheduler trace
  have count := PhaseCount.countRecall_history runtime leaks rawTrace
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
  obtain ⟨message, emitted, sender, call⟩ :=
    PhaseCount.recalled_submission_emitted runtime leaks initial horizon scheduler rawTrace owner
      entry recorded material (by rw [declared])
  have output : message ∈ (app).outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, recorded, emitted⟩
  rw [← count.1 owner] at output
  have member : message ∈ original.network.inputs := by
    rw [network]
    exact (List.mem_filter.mp output).1
  obtain ⟨value, successful⟩ :=
    (prepared message member sender event (owner, .prepared serial) call payload outputEq codeEq
      node).2.2.1
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _recalled⟩ :=
    menu.recorded_response_prefix initial horizon scheduler control trace owner entry recorded
  rw [declared] at offered
  have fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh :=
    viewed ▸ PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler
      prior owner event serial opening evidence offered
  have meaning := phase_recorded_material_binding_result runtime leaks menu initial horizon
    scheduler control trace owner event payload serial opening evidence entry recorded declared
      fresh
  rw [meaning] at successful
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | none =>
      simp only [decoded, Option.elim_none] at successful
      cases successful
  | some value => exact ⟨value, rfl⟩

end Vegas.EventGraphRuntime.BindingShadow
