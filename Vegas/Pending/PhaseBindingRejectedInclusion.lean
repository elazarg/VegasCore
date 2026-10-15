/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRejectedReplay
import Vegas.Pending.EventPublicState

/-! # Publicly blocked native calls during a physical binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

private theorem rejected_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (leftRejected : handle runtime original.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = none)
    (rightRejected : handle runtime repaired.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = none) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  let app := phaseApplication runtime leaks
  have rightFound : repaired.network.lookup id = some message := frame.network ▸ found
  have leftNone : (phaseApplication runtime leaks).handle original.application message = none := by
    change original.application.handle runtime message = none
    unfold PhaseRuntimeState.handle
    split
    · rw [leftRejected]
      rfl
    · rfl
  have rightNone : (phaseApplication runtime leaks).handle repaired.application message = none := by
    change repaired.application.handle runtime message = none
    unfold PhaseRuntimeState.handle
    split
    · rw [rightRejected]
      rfl
    · rfl
  have logs : original.environmentRecall ++
      [⟨original.observeEnvironment app, .include id⟩] =
      repaired.environmentRecall ++ [⟨repaired.observeEnvironment app, .include id⟩] := by
    rw [frame.service, frame.environment_input]
  have next := frame.with_physics (original.network.includePending id).2
    (original.receipts ++ [(id, false)]) _ _ logs
  have receipts : original.receipts = repaired.receipts := frame.live.receipts
  simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    found, rightFound, leftNone, rightNone, Option.getD_none, Option.isSome_none,
    ← frame.network, ← receipts] using next

/-- A commitment blocked by the public native acceptance conditions rejects
on both sides, even if its private immutable candidates differ. -/
theorem binding_not_includable
    (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (blocked : ¬original.application.current.native.publicView.BindingIncludable runtime
      ⟨message.id, .commitment event candidate⟩) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  have refused (state : State graph)
      (publicEq : state.publicView = original.application.current.native.publicView) :
      handle runtime state ⟨message.id, .commitment event candidate⟩ = none := by
    cases handled : handle runtime state ⟨message.id, .commitment event candidate⟩ with
    | none => rfl
    | some next =>
        apply False.elim
        apply blocked
        rw [← publicEq]
        apply (state.publicView_bindingIncludable runtime message.id event candidate).mpr
        rw [handled]
        rfl
  apply frame.rejected_inclusion id message found
  · rw [call]
    exact refused original.application.current.native rfl
  · rw [call]
    exact refused repaired.application.current.native frame.live.publicView.symm

/-- An opening whose source event is not ready is rejected independently of
private catalogues and guards; readiness is part of the common public frame. -/
theorem opening_not_ready
    (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (call : message.payload.packet.call = .opening event candidate raw)
    (blocked : ¬original.application.current.native.config.cut.Ready event) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  have visible : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  have rightBlocked : ¬repaired.application.current.native.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← visible, State.publicView_eventReady]
    exact blocked
  apply frame.rejected_inclusion id message found
  · simp only [call, handle, dite_eq_right blocked]
  · simp only [call, handle, dite_eq_right rightBlocked]

/-- A physically late opening is rejected on both sides by the actual common
clock and readiness stamp, before any hidden value or guard is inspected. -/
theorem opening_late
    (frame : Frame runtime leaks memory owner original repaired)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (call : message.payload.packet.call = .opening event candidate raw)
    (blocked : ¬original.application.current.native.WithinDeadline runtime event) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks), .include id⟩] } := by
  have clocks : original.application.current.native.clock =
      repaired.application.current.native.clock := congrArg PublicView.clock frame.live.publicView
  have stamps : original.application.current.native.activatedAt =
      repaired.application.current.native.activatedAt :=
    congrArg PublicView.activatedAt frame.live.publicView
  have rightBlocked : ¬repaired.application.current.native.WithinDeadline runtime event := by
    unfold State.WithinDeadline at blocked ⊢
    rwa [← clocks, ← stamps]
  apply frame.rejected_inclusion id message found
  · simp [call, handle, blocked]
  · simp [call, handle, rightBlocked]

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
