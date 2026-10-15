/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingInclusionFrame
import Vegas.Pending.ReactiveBindingFrameForeign

/-! # Actual foreign binding inclusion during a phased private repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- A different player's actual fixed candidate is included on both sides.
Its typed result may be failure: source-semantic failure is never identified
with an omitted or publicly excluded physical commitment. -/
theorem foreign_binding_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
    (found : original.network.lookup id = some message)
    (event : graph.EventId) (candidate : Handle graph)
    (actor : Player) (different : actor ≠ owner) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding actor payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind actor payload)
    (node : nodeView graph event = .bind actor payload outputEq codeEq)
    (ready : original.application.current.native.config.cut.Ready event)
    (timely : original.application.current.native.WithinDeadline runtime event)
    (sender : id.1 = actor) (owned : candidate.1 = actor)
    (vacant : original.application.current.native.accepted (.inr event) = none)
    (unused : original.application.current.native.HandleUnused candidate)
    (fixed : original.application.current.native.candidates.lookup candidate ≠ .fresh)
    (evidence : Option (OpeningFact graph))
    (packet : PhaseCount.nativeMessage message =
      ⟨id, ⟨.commitment event candidate, evidence, some ⟨event⟩⟩⟩)
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
      some ⟨id, ⟨.commitment event candidate, evidence, some ⟨event⟩⟩⟩ := by
    change (PhaseBindingRepair.network original.network).lookup id = _
    rw [network_lookup, found, Option.map_some, packet]
  have native := frame.live.foreign_binding_inclusion onlyBindings id event candidate actor
    different payload outputEq codeEq node ready timely sender owned vacant unused fixed
    evidence nativeFound
  have candidates : original.application.current.native.candidates.lookup candidate =
      repaired.application.current.native.candidates.lookup candidate := by
    have seen := congrArg PlayerView.candidates (frame.live.views actor different)
    have handleEq : candidate = (actor, candidate.2) := Prod.ext owned rfl
    rw [handleEq]
    exact congrFun seen candidate.2
  have rightFixed : repaired.application.current.native.candidates.lookup candidate ≠ .fresh :=
    candidates ▸ fixed
  have visible : original.application.current.native.publicView =
      repaired.application.current.native.publicView := frame.live.publicView
  have rightReady : repaired.application.current.native.config.cut.Ready event := by
    rw [← State.publicView_eventReady, ← visible, State.publicView_eventReady]
    exact ready
  have clocks : original.application.current.native.clock =
      repaired.application.current.native.clock := congrArg PublicView.clock frame.live.publicView
  have activations : original.application.current.native.activatedAt =
      repaired.application.current.native.activatedAt :=
    congrArg PublicView.activatedAt frame.live.publicView
  have accepted : original.application.current.native.accepted =
      repaired.application.current.native.accepted :=
    congrArg PublicView.accepted frame.live.publicView
  have rightTimely : repaired.application.current.native.WithinDeadline runtime event := by
    unfold State.WithinDeadline at timely ⊢
    rwa [← clocks, ← activations]
  have rightVacant : repaired.application.current.native.accepted (.inr event) = none := by
    rw [← accepted]
    exact vacant
  have rightUnused : repaired.application.current.native.HandleUnused candidate := by
    intro field installed
    exact unused field ((congrFun accepted field).trans installed)
  have messageId : message.id = id := congrArg Message.id packet
  have call : message.payload.packet.call = .commitment event candidate :=
    congrArg (fun item : Message Player (WitnessedPacket graph) => item.payload.call) packet
  let leftNative : State graph := {
    (original.application.current.native.complete event ready
      (cast (congrArg EventField.Action outputEq.symm)
        (original.application.current.native.bindingResult candidate payload))
      (cast (congrArg EventField.Value outputEq.symm)
        (original.application.current.native.bindingResult candidate payload))) with
    accepted := Function.update original.application.current.native.accepted (.inr event)
      (some candidate) }
  let rightNative : State graph := {
    (repaired.application.current.native.complete event rightReady
      (cast (congrArg EventField.Action outputEq.symm)
        (repaired.application.current.native.bindingResult candidate payload))
      (cast (congrArg EventField.Value outputEq.symm)
        (repaired.application.current.native.bindingResult candidate payload))) with
    accepted := Function.update repaired.application.current.native.accepted (.inr event)
      (some candidate) }
  have leftHandled : handle runtime original.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some leftNative := by
    rw [messageId, call, handle_commitment_eq runtime _ id event candidate actor payload
      outputEq codeEq node ready timely sender owned vacant unused,
      original.application.current.native.candidates.freeze_eq_self_of_not_fresh candidate fixed]
    rfl
  have rightHandled : handle runtime repaired.application.current.native
      ⟨message.id, message.payload.packet.call⟩ = some rightNative := by
    rw [messageId, call, handle_commitment_eq runtime _ id event candidate actor payload
      outputEq codeEq node rightReady rightTimely sender owned rightVacant rightUnused,
      repaired.application.current.native.candidates.freeze_eq_self_of_not_fresh candidate
        rightFixed]
    rfl
  exact frame.admitted_inclusion id message found admitted leftNative rightNative leftHandled
    rightHandled rfl rfl native clear

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
