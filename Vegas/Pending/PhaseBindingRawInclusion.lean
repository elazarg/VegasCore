/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingNativeInclusion
import Vegas.Pending.PhaseBindingRepairNormalize

/-! # Raw binding edges before automatic clean phase installation -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- The native include effect, with the actual physical ledger and unchanged
saved checkpoint. Automatic phase installation is applied only afterward. -/
def rawBindingInclude (physical : (phaseApplication runtime leaks).Execution)
    (id : MessageId Player) : (phaseApplication runtime leaks).Execution :=
  let native := (execution runtime leaks physical).includePending
    (runtime.reactiveApplication (nativeLeaks (graph := graph))) id
  { physical with
    application := { physical.application with
      current := ⟨native.application, physical.application.current.excluded⟩ }
    network := (physical.network.includePending id).2
    receipts := native.receipts }

theorem execution_rawBindingInclude
    (physical : (phaseApplication runtime leaks).Execution) (id : MessageId Player) :
    execution runtime leaks (rawBindingInclude runtime leaks physical id) =
      (execution runtime leaks physical).includePending
        (runtime.reactiveApplication (nativeLeaks (graph := graph))) id := by
  let native := (execution runtime leaks physical).includePending
    (runtime.reactiveApplication (nativeLeaks (graph := graph))) id
  have packets := network_include physical.network id
  have nativeNetwork : native.network = ((network physical.network).includePending id).2 := by
    change native.network = ((execution runtime leaks physical).network.includePending id).2
    unfold native ReactiveApplication.Execution.includePending
    cases result : (execution runtime leaks physical).network.includePending id with
    | mk message pool => cases message <;> rfl
  have nativeRecall : native.recall = (execution runtime leaks physical).recall := by
    unfold native ReactiveApplication.Execution.includePending
    cases result : (execution runtime leaks physical).network.includePending id with
    | mk message pool => cases message <;> rfl
  have nativeService : native.environmentRecall =
      (execution runtime leaks physical).environmentRecall := by
    unfold native ReactiveApplication.Execution.includePending
    cases result : (execution runtime leaks physical).network.includePending id with
    | mk message pool => cases message <;> rfl
  change (⟨native.application, network (physical.network.includePending id).2, native.receipts,
    (execution runtime leaks physical).recall,
    (execution runtime leaks physical).environmentRecall⟩ :
      (runtime.reactiveApplication (nativeLeaks (graph := graph))).Execution) =
        ⟨native.application, native.network, native.receipts, native.recall,
          native.environmentRecall⟩
  rw [nativeNetwork, nativeRecall, nativeService, packets]

/-- The actual phased include is the raw native edge followed by the genuine
normalizer. No claim of persistent semantic completion across rollback is needed. -/
theorem include_binding_eq_normalize
    (physical : (phaseApplication runtime leaks).Execution) (id : MessageId Player)
    (message : Message Player (CommitAttemptPacket graph))
    (found : physical.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (admitted : (message.payload.tokenValid physical.application.attempt &&
      physical.application.allows message.payload.packet.call &&
      !physical.application.current.excludedCall message.payload.packet.call) = true)
    (native : State graph)
    (handled : handle runtime physical.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    physical.includePending (phaseApplication runtime leaks) id =
      PhaseRuntimeState.normalizeExecution runtime leaks
        (rawBindingInclude runtime leaks physical id) := by
  have nativeToken : message.payload.packet.tokenValid = true :=
    (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).1).2
  have nativeFound : (network physical.network).lookup id =
      some (PhaseCount.nativeMessage message) := by rw [network_lookup, found]; rfl
  have effect : (execution runtime leaks physical).includePending
      (runtime.reactiveApplication (nativeLeaks (graph := graph))) id =
      { execution runtime leaks physical with
        application := native
        network := ((network physical.network).includePending id).2
        receipts := physical.receipts ++ [(id, true)] } := by
    unfold ReactiveApplication.Execution.includePending
    dsimp only [execution]
    simp only [MessageNetwork.includePending, nativeFound, reactiveApplication_handle,
      PhaseCount.nativeMessage, nativeToken, ite_true, handled, Option.getD_some,
      Option.isSome_some]
  unfold rawBindingInclude
  rw [effect]
  unfold ReactiveApplication.Execution.includePending
  simp only [MessageNetwork.includePending, found, PhaseRuntimeState.normalizeExecution,
    phaseApplication, PhaseRuntimeState.handle, admitted, ite_true, handled,
    Option.map_some, Option.getD_some, Option.isSome_some]
  rw [call]
  rfl

end Vegas.EventGraphRuntime.PhaseBindingRepair
