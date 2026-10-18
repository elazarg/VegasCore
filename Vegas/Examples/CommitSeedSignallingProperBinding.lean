/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingContinuation
import Vegas.Pending.PhaseBindingService
import Vegas.Pending.PhaseRecordedBindingMeaning
import Vegas.Pending.ReactiveSeedBindingReadout

/-! # Native acceptance of the actual proper binding declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- A remembered fresh TRUE declaration is accepted by the actual native
handler while its original request remains ready and timely. The raw completed
configuration writes TRUE even when normalization immediately retires it. -/
theorem recorded_true_binding_accepted
    (selected : app.Scheduler) (control : app.Control)
    (trace : (countedMenu.protocol initial horizon selected).Trace (some control))
    (who : Player) (event : graph.EventId)
    (outputEq : graph.outputLayout event = .binding who .bool)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      EventCode.bind (L := simpleExpr) (layout := graph.layout) who BaseTy.bool)
    (node : nodeView graph event = .bind who .bool outputEq codeEq)
    (serial : Nat) (entry : app.PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (declared : entry.action =
      phaseBindingResponse runtime leaks who event .bool (.success true) serial)
    (fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (sender : message.sender = who)
    (call : message.payload.packet.call = .commitment event (who, .prepared serial))
    (request : control.execution.application.SeedRequest who
      ⟨message.payload.attempt, event⟩)
    (timely : control.execution.application.current.native.WithinDeadline runtime event) :
    ∃ native next,
      handle runtime control.execution.application.current.native
        ⟨message.id, .commitment event (who, .prepared serial)⟩ = some native ∧
      event ∈ native.config.cut.completed ∧
      native.accepted (.inr event) = some (who, .prepared serial) ∧
      native.config.outputs event = some
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.success true : PublicationResult (simpleExpr.Val .bool))) ∧
      next = ({control.execution.application with current :=
        control.execution.application.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph).normalize ∧
      app.handle control.execution.application message = some next := by
  classical
  have raw := countedMenu.toRawTrace initial horizon selected trace
  have meaning := phase_recorded_binding_result runtime leaks initial horizon selected raw
    who event .bool (.success true) serial entry retained declared fresh
  have actualRequest : control.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩ := by
    rw [sender]
    exact request
  obtain ⟨native, next, handled, completed, accepted, normalized, phaseHandled⟩ :=
    PhaseCount.binding_accepted_of_history runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon selected trace message member event
      (who, .prepared serial) call actualRequest timely
  have rawHandled : handle runtime control.execution.application.current.native
      ⟨message.id, .commitment event (who, .prepared serial)⟩ = some native := by
    simpa only [call] using handled
  obtain ⟨ready, configEq⟩ := runtime.handle_commitment_config_result
    control.execution.application.current.native native message.id event
    (who, .prepared serial) who .bool outputEq codeEq node rawHandled
  have output : native.config.outputs event = some
      (cast (congrArg EventField.Value outputEq.symm)
        (PublicationResult.success true : PublicationResult (simpleExpr.Val .bool))) := by
    rw [configEq, Config.complete_output_same, meaning]
  exact ⟨native, next, rawHandled, completed, accepted, output, normalized, phaseHandled⟩

end Vegas.Examples.CommitSeedSignalling
