/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperSubmittedPublication
import Vegas.Pending.PhaseRecordedBindingMaterial

/-! # Successful native readback for arbitrary usable helper preparations -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol
open OnePacketCommitRevealHypotheses (Player alice)

/-- An actually admitted helper packet writes the Boolean supplied by its
original fresh preparation. Its evidence and preparation representation are
arbitrary, and no successful-output premise is supplied. -/
theorem helper_usable_packet_native_output (selected : app.Scheduler)
    (current : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some current))
    (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall alice)
    (serial : Nat) (opening : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph)
    (declared : entry.action =
      ⟨some ⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), opening⟩, evidence⟩⟩)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (value : Bool) (usable : (opening.bind fun raw => raw.as? .bool) = some value)
    (message : Message Player (CommitAttemptPacket graph))
    (call : message.payload.packet.call =
      .commitment (bindingEvent alice) (alice, .prepared serial))
    (native : EventGraphRuntime.State graph)
    (handled : handle runtime current.execution.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    native.config.outputs (bindingEvent alice) = some
      (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
        (PublicationResult.success value : PublicationResult (simpleExpr.Val .bool))) := by
  have meaning := phase_recorded_material_binding_result runtime leaks countedMenu initial horizon
    selected current trace alice (bindingEvent alice) .bool serial opening evidence entry recorded
      declared fresh
  rw [usable, Option.elim_some] at meaning
  have codeEq : cast (congrArg (EventCode graph.layout) (bindingEvent_layout alice))
      (graph.nodes (bindingEvent alice)) = EventCode.bind (L := simpleExpr)
        (layout := graph.layout) alice BaseTy.bool := by rfl
  have node : nodeView graph (bindingEvent alice) =
      .bind alice .bool (bindingEvent_layout alice) codeEq := by rfl
  have rawHandled : handle runtime current.execution.application.current.native
      ⟨message.id, .commitment (bindingEvent alice) (alice, .prepared serial)⟩ = some native := by
    simpa only [call] using handled
  obtain ⟨_ready, configEq⟩ := runtime.handle_commitment_config_result
    current.execution.application.current.native native message.id (bindingEvent alice)
      (alice, .prepared serial) alice .bool (bindingEvent_layout alice) codeEq node rawHandled
  rw [configEq, Config.complete_output_same, meaning]

end Vegas.Examples.CommitSeedSignalling
