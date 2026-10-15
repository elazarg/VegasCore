/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCheckpointFrame

/-! # Actual binding inclusion projects through clear phase installation -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

private theorem find_native (messages : List (Message Player (CommitAttemptPacket graph)))
    (id : MessageId Player) :
    (messages.map PhaseCount.nativeMessage).find? (fun message => message.id = id) =
      (messages.find? (fun message => message.id = id)).map PhaseCount.nativeMessage := by
  induction messages with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first.id = id <;>
        simp only [List.map_cons, List.find?_cons, PhaseCount.nativeMessage, same,
          decide_true, decide_false, ih, Option.map_some]

theorem network_lookup (physical : MessageNetwork Player (CommitAttemptPacket graph))
    (id : MessageId Player) :
    (network physical).lookup id = (physical.lookup id).map PhaseCount.nativeMessage :=
  find_native physical.pending id

private theorem remove_native (messages : List (Message Player (CommitAttemptPacket graph)))
    (id : MessageId Player) :
    (MessagePool.removeFirst id messages).map PhaseCount.nativeMessage =
      MessagePool.removeFirst id (messages.map PhaseCount.nativeMessage) := by
  induction messages with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first.id = id <;>
        simp only [List.map_cons, MessagePool.removeFirst, PhaseCount.nativeMessage, same,
          ite_true, ite_false, ih]

theorem network_include (physical : MessageNetwork Player (CommitAttemptPacket graph))
    (id : MessageId Player) :
    network (physical.includePending id).2 = ((network physical).includePending id).2 := by
  simp only [MessageNetwork.includePending, network_lookup]
  cases found : physical.lookup id with
  | none => rfl
  | some message =>
      simp only [Option.map_some, network, List.map_append, List.map_cons, List.map_nil,
        remove_native]

/-- A current admitted binding uses the native handler and retains its exact
raw result through clear phase installation, including privately unusable results. -/
theorem handle_binding_native (state : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (admitted : (message.payload.tokenValid state.attempt &&
      state.allows message.payload.packet.call &&
      !state.current.excludedCall message.payload.packet.call) = true)
    (clear : state.current.excluded = ∅) :
    (state.handle runtime message).map (fun next => next.current.native) =
      (runtime.reactiveApplication (nativeLeaks (graph := graph))).handle
        state.current.native (PhaseCount.nativeMessage message) := by
  have token := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).1
  have nativeToken : message.payload.packet.tokenValid = true :=
    (Bool.and_eq_true_iff.mp token).2
  simp only [PhaseRuntimeState.handle, admitted, ite_true, reactiveApplication_handle,
    PhaseCount.nativeMessage, nativeToken, ite_true]
  cases handled : handle runtime state.current.native
      ⟨message.id, message.payload.packet.call⟩ with
  | none => rfl
  | some native =>
      simp only [Option.map_some]
      have rawClear : (state.current.inclusionResult message.payload.packet.call native).excluded =
          ∅ := by rw [call]; exact clear
      have installed := PhaseRuntimeState.settle_of_clear state.phases state.generation state.entry
        (state.current.inclusionResult message.payload.packet.call native) state.retired rawClear
      exact congrArg (some ∘ RecoveryState.native) installed.1

/-- Physical publication of an admitted current binding has exactly the native
network, receipt, recall and semantic image. The scheduler remains the phased one. -/
theorem execution_include_binding (physical : (phaseApplication runtime leaks).Execution)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : physical.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (admitted : (message.payload.tokenValid physical.application.attempt &&
      physical.application.allows message.payload.packet.call &&
      !physical.application.current.excludedCall message.payload.packet.call) = true)
    (clear : physical.application.current.excluded = ∅) :
    execution runtime leaks (physical.includePending (phaseApplication runtime leaks) id) =
      (execution runtime leaks physical).includePending
        (runtime.reactiveApplication (nativeLeaks (graph := graph))) id := by
  have nativeFound : (network physical.network).lookup id =
      some (PhaseCount.nativeMessage message) := by rw [network_lookup, found]; rfl
  have image := handle_binding_native runtime physical.application message event candidate
    call admitted clear
  have packets := network_include physical.network id
  simp only [MessageNetwork.includePending, found, nativeFound] at packets
  unfold ReactiveApplication.Execution.includePending
  simp only [MessageNetwork.includePending, found, execution, nativeFound]
  change (⟨((physical.application.handle runtime message).getD physical.application).current.native,
    _, _, _, _⟩ : (runtime.reactiveApplication (nativeLeaks (graph := graph))).Execution) = _
  cases handled : physical.application.handle runtime message with
  | none =>
      rw [handled, Option.map_none] at image
      rw [← image]
      simpa only [phaseApplication, handled, Option.getD_none, Option.getD_some,
        Option.isSome_none, Option.isSome_some] using congrArg (fun pool =>
        (⟨physical.application.current.native, pool,
        physical.receipts ++ [(id, false)],
        fun who => (physical.recall who).map (entry runtime leaks),
        physical.environmentRecall.map (environmentEntry runtime leaks)⟩ :
          (runtime.reactiveApplication (nativeLeaks (graph := graph))).Execution)) packets
  | some next =>
      rw [handled, Option.map_some] at image
      rw [← image]
      simpa only [phaseApplication, handled, Option.getD_none, Option.getD_some,
        Option.isSome_none, Option.isSome_some] using congrArg (fun pool =>
        (⟨next.current.native, pool,
        physical.receipts ++ [(id, true)],
        fun who => (physical.recall who).map (entry runtime leaks),
        physical.environmentRecall.map (environmentEntry runtime leaks)⟩ :
          (runtime.reactiveApplication (nativeLeaks (graph := graph))).Execution)) packets

end Vegas.EventGraphRuntime.PhaseBindingRepair
