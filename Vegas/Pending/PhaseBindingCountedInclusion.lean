/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCountedForeign
import Vegas.Pending.PhaseBindingRejectedInclusion
import Vegas.Pending.ReactiveBindingSubmittedRecords

/-! # Every actual counted commitment inclusion preserves the phased frame -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The submitted-binding record is the induction invariant established at
repair responses. It supplies delayed own inclusion; other owners and actual
rejections are discharged by the original counted history and public gate. -/
theorem counted_binding_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (recorded : memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
      (execution runtime leaks original) (execution runtime leaks repaired))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat) (actorTurn : Option Player)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, actorTurn, original⟩))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ original.network.inputs)
    (found : original.network.lookup message.id = some message)
    (event : graph.EventId) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (clear : (original.includePending (phaseApplication runtime leaks)
      message.id).application.current.excluded = ∅) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) message.id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include message.id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) message.id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks),
            .include message.id⟩] } := by
  by_cases admitted : (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) = true
  · by_cases includable : original.application.current.native.publicView.BindingIncludable runtime
        ⟨message.id, .commitment event candidate⟩
    · by_cases foreign : message.sender ≠ owner
      · exact frame.counted_foreign_binding_inclusion onlyBindings bounds plan inputs horizon
          scheduler remaining actorTurn trace message member found event candidate call foreign
          includable admitted clear
      · have sender : message.sender = owner := not_ne_iff.mp foreign
        have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs
          horizon scheduler trace
        have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (physical.clean.2 message member)
        have correct := permitted.2.1
        unfold CountCallCorrect at correct
        dsimp only [PhaseCount.nativeMessage] at correct
        rw [call] at correct
        obtain ⟨bindingOwned, noEvidence, candidateOwned, _⟩ := correct
        obtain ⟨named, addressed, attached⟩ :=
          (WitnessedPacket.tokenValid_iff message.payload.packet).mp permitted.1
        have sameEvent : named = event := by
          have same := addressed
          rw [call] at same
          exact Option.some.inj same.symm
        subst named
        have packet : PhaseCount.nativeMessage message =
            ⟨message.id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩ := by
          change (⟨message.id, ⟨message.payload.packet.call, message.payload.packet.evidence,
            message.payload.packet.token⟩⟩ : Message Player (WitnessedPacket graph)) = _
          rw [call, noEvidence, attached]
        cases node : nodeView graph event with
        | sample payload law outputEq codeEq =>
            simp only [bindingOwnedBy, outputEq] at bindingOwned
            cases bindingOwned
        | resolve actor payload binding checks outputEq codeEq =>
            simp only [bindingOwnedBy, outputEq] at bindingOwned
            cases bindingOwned
        | bind actor payload outputEq codeEq =>
            have actorEq : actor = owner := by
              simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq, Message.sender,
                show message.id.1 = owner from sender] using bindingOwned
            subst actor
            have owned : candidate.1 = owner := candidateOwned.trans sender
            simp only [PublicView.BindingIncludable, node] at includable
            change original.application.current.native.publicView.EventReady event ∧
              original.application.current.native.WithinDeadline runtime event ∧ _ at includable
            obtain ⟨publicReady, timely, conditions⟩ := includable
            have ready :=
              (original.application.current.native.publicView_eventReady event).mp publicReady
            change message.id.1 = owner ∧ candidate.1 = owner ∧
              original.application.current.native.accepted (.inr event) = none ∧
                original.application.current.native.HandleUnused candidate at conditions
            obtain ⟨_, _, vacant, unused⟩ := conditions
            have nativeMember : PhaseCount.nativeMessage message ∈
                (execution runtime leaks original).network.inputs :=
              List.mem_map.mpr ⟨message, member, rfl⟩
            obtain ⟨remembered, leftFixed, rightFixed, _, successes⟩ := recorded
              (PhaseCount.nativeMessage message) nativeMember sender event candidate call
                payload outputEq codeEq node
            exact frame.binding_inclusion event payload outputEq codeEq node message.id candidate
              sender owned message found packet admitted ready timely vacant unused leftFixed
              rightFixed remembered.1 remembered.2 successes
    · exact frame.binding_not_includable message.id message found event candidate call includable
  · exact frame.include_unauthorized message.id message found (Bool.eq_false_iff.mpr admitted)

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
