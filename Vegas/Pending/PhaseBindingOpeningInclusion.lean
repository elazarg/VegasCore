/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingInclusionFrame
import Vegas.Pending.ReactiveBindingFrameOpening

/-! # Physical inclusion of unchanged successful bindings during repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Actual opening inclusion preserves both frontiers and the physical ledger.
The checked deferred-guard result is retained; clear source survival determines
that the image also avoids a new exclusion before phase installation. -/
theorem opening_inclusion (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (ready : original.application.current.native.config.cut.Ready event)
    (timely : original.application.current.native.WithinDeadline runtime event)
    (sender : id.1 = actor) (owned : candidate.1 = actor)
    (associated : original.application.current.native.accepted binding.field = some candidate)
    (value : L.Val payload)
    (leftFixed : original.application.current.native.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (rightFixed : repaired.application.current.native.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (leftStored : binding.get? original.application.current.native.config.store =
      some (.success value))
    (rightStored : binding.get? repaired.application.current.native.config.store =
      some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true
      original.application.current.native.config.store = some result)
    (evidence : Option (OpeningFact graph))
    (packet : PhaseCount.nativeMessage message =
      ⟨id, ⟨.opening event candidate ⟨payload, value⟩, evidence, some ⟨event⟩⟩⟩)
    (admitted : (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) = true)
    (clear : (original.includePending (phaseApplication runtime leaks)
      id).application.current.excluded = ∅) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  have nativeFound : (execution runtime leaks original).network.lookup id =
      some ⟨id, ⟨.opening event candidate ⟨payload, value⟩, evidence, some ⟨event⟩⟩⟩ := by
    change (PhaseBindingRepair.network original.network).lookup id = _
    rw [network_lookup, found, Option.map_some, packet]
  have native := frame.live.opening_inclusion onlyBindings id event candidate actor payload
    binding checks outputEq codeEq node ready timely sender owned associated value leftFixed
    rightFixed leftStored rightStored result resolved evidence nativeFound
  obtain ⟨rightReady, rightTimely, rightAssociated, rightResolved⟩ :=
    opening_right_facts runtime original.application.current.native
      repaired.application.current.native frame.live.publicView event actor payload binding checks
      candidate ready timely associated value leftStored rightStored result resolved
  have messageId : message.id = id := congrArg Message.id packet
  have call : message.payload.packet.call = .opening event candidate ⟨payload, value⟩ :=
    congrArg (fun item : Message Player (WitnessedPacket graph) => item.payload.call) packet
  have leftHandled := handle_opening_eq runtime original.application.current.native id event
    candidate actor payload binding checks outputEq codeEq node ready timely sender owned associated
      value leftFixed leftStored result resolved
  have rightHandled := handle_opening_eq runtime repaired.application.current.native id event
    candidate actor payload binding checks outputEq codeEq node rightReady rightTimely sender owned
      rightAssociated value rightFixed rightStored result rightResolved
  apply frame.admitted_inclusion id message found admitted
    (original.application.current.native.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) true)
      (cast (congrArg EventField.Value outputEq.symm) result))
    (repaired.application.current.native.complete event rightReady
      (cast (congrArg EventField.Action outputEq.symm) true)
      (cast (congrArg EventField.Value outputEq.symm) result)) _ _ rfl rfl native clear
  · simpa only [messageId, call] using leftHandled
  · simpa only [messageId, call] using rightHandled

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
