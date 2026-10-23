/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingFrame

/-! # Rejected pending inclusion through a binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Common network and receipt updates preserve reconstructed own observations
and all foreign application inputs. -/
theorem withNetworkReceipts (frame : Frame runtime leaks memory owner original repaired)
    (network : MessageNetwork Player (WitnessedPacket graph))
    (receipts : List (MessageId Player × Bool)) :
    Frame runtime leaks memory owner { original with network := network, receipts := receipts }
      { repaired with network := network, receipts := receipts } := by
  refine ⟨frame.past, ?_, frame.lengths, rfl, frame.service, frame.views, frame.recall,
    frame.slots, frame.successful, frame.submissions⟩
  have applications := congrArg ReactiveApplication.PlayerView.application frame.observed
  exact congrArg (fun view => (⟨network.observe owner, view, receipts⟩ :
    (runtime.reactiveApplication leaks).PlayerView)) applications

/-- Recording the same actual environment command preserves the private frame. -/
theorem recordEnvironment (frame : Frame runtime leaks memory owner original repaired)
    (command : (runtime.reactiveApplication leaks).Command) :
    Frame runtime leaks memory owner
      { original with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment (runtime.reactiveApplication leaks), command⟩] }
      { repaired with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment (runtime.reactiveApplication leaks), command⟩] } := by
  exact { frame with service := by rw [frame.service, frame.environment] }

/-- A missing identifier stutters jointly, including its public command recall. -/
theorem include_missing (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (missing : original.network.lookup id = none) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  have rightMissing : repaired.network.lookup id = none := frame.network ▸ missing
  simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    missing, rightMissing] using frame.recordEnvironment (.include id)

/-- A jointly rejected real envelope has the same failed public receipt and
network update. No private store or candidate assumptions are required. -/
theorem include_rejected (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : original.network.lookup id = some message)
    (leftRejected : (runtime.reactiveApplication leaks).handle original.application message = none)
    (rightRejected :
      (runtime.reactiveApplication leaks).handle repaired.application message = none) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  have rightFound : repaired.network.lookup id = some message := frame.network ▸ found
  have next := frame.withNetworkReceipts (original.network.includePending id).2
    (original.receipts ++ [(id, false)])
  have logged : Frame runtime leaks memory owner
      { original with
        network := (original.network.includePending id).2
        receipts := original.receipts ++ [(id, false)]
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (runtime.reactiveApplication leaks), .include id⟩] }
      { repaired with
        network := (original.network.includePending id).2
        receipts := original.receipts ++ [(id, false)]
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (runtime.reactiveApplication leaks), .include id⟩] } :=
    { next with service := by rw [frame.service, frame.environment] }
  change Frame runtime leaks memory owner _ _
  simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, rightFound, leftRejected, rightRejected, Option.getD_none, Option.isSome_none,
    ← frame.network, ← frame.receipts] using logged

end Vegas.EventGraphRuntime.BindingMemory.Frame
