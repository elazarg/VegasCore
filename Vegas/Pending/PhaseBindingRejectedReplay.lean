/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSilentResponse
import Vegas.Pending.ReactiveBindingRejectedInclusion

/-! # Actual missing and publicly unauthorized phased inclusions -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A common physical network and receipt update preserves both application
frontiers. Equal actual scheduler logs may retain the pre-command observation. -/
theorem with_physics (frame : Frame runtime leaks memory owner original repaired)
    (pool : MessageNetwork Player (CommitAttemptPacket graph))
    (receipts : List (MessageId Player × Bool))
    (leftLog rightLog : List (phaseApplication runtime leaks).EnvironmentEntry)
    (logs : leftLog = rightLog) :
    Frame runtime leaks memory owner
      { original with network := pool, receipts := receipts, environmentRecall := leftLog }
      { repaired with network := pool, receipts := receipts, environmentRecall := rightLog } := by
  have live := frame.live.withNetworkReceipts (PhaseBindingRepair.network pool) receipts
  have saved := frame.saved.withNetworkReceipts (PhaseBindingRepair.network pool) receipts
  refine ⟨?_, ?_, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
    frame.archiveOriginal, frame.archiveRepaired, rfl, logs, frame.foreignRecall⟩
  · exact { live with service := congrArg (List.map (environmentEntry runtime leaks)) logs }
  · exact { saved with service := congrArg (List.map (environmentEntry runtime leaks)) logs }

/-- Appending a public command leaves the full reconstructed private inputs
unchanged. The observations recorded are those of the actual original prefixes. -/
theorem record_environment (frame : Frame runtime leaks memory owner original repaired)
    (chosen : (phaseApplication runtime leaks).Command) :
    Frame runtime leaks memory owner
      { original with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment (phaseApplication runtime leaks), chosen⟩] }
      { repaired with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment (phaseApplication runtime leaks), chosen⟩] } := by
  have logs : original.environmentRecall ++
      [⟨original.observeEnvironment (phaseApplication runtime leaks), chosen⟩] =
        repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), chosen⟩] := by
    rw [frame.service, frame.environment_input]
  refine ⟨?_, ?_, frame.phases, frame.generation, frame.clearOriginal, frame.clearRepaired,
    frame.archiveOriginal, frame.archiveRepaired, frame.network, logs, frame.foreignRecall⟩
  · exact { frame.live with
      service := congrArg (List.map (environmentEntry runtime leaks)) logs }
  · exact { frame.saved with
      service := congrArg (List.map (environmentEntry runtime leaks)) logs }

/-- A missing physical identifier gives the same actual stuttering include,
including the original scheduler's complete command recall. -/
theorem include_missing (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (missing : original.network.lookup id = none) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  have rightMissing : repaired.network.lookup id = none := frame.network ▸ missing
  simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    missing, rightMissing] using frame.record_environment (.include id)

/-- A stale namespace or publicly unauthorized packet is rejected on both
sides by the actual phase gate. No target handler outcome is assumed. -/
theorem include_unauthorized (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (denied : (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) = false) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  let app := phaseApplication runtime leaks
  have rightFound : repaired.network.lookup id = some message := frame.network ▸ found
  have rightDenied : (message.payload.tokenValid repaired.application.attempt &&
      repaired.application.allows message.payload.packet.call &&
      !repaired.application.current.excludedCall message.payload.packet.call) = false :=
    (frame.admission message).symm.trans denied
  have leftRejected : (phaseApplication runtime leaks).handle original.application message =
      none := by
    change original.application.handle runtime message = none
    simp only [PhaseRuntimeState.handle, denied, Bool.false_eq_true, ite_false]
  have rightRejected : (phaseApplication runtime leaks).handle repaired.application message =
      none := by
    change repaired.application.handle runtime message = none
    simp only [PhaseRuntimeState.handle, rightDenied, Bool.false_eq_true, ite_false]
  have logs : original.environmentRecall ++
      [⟨original.observeEnvironment app, .include id⟩] =
      repaired.environmentRecall ++ [⟨repaired.observeEnvironment app, .include id⟩] := by
    rw [frame.service, frame.environment_input]
  have next := frame.with_physics (original.network.includePending id).2
    (original.receipts ++ [(id, false)]) _ _ logs
  have receipts : original.receipts = repaired.receipts := frame.live.receipts
  simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, rightFound, leftRejected, rightRejected, Option.getD_none, Option.isSome_none,
    ← frame.network, ← receipts] using next

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
