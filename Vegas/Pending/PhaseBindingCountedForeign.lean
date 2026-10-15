/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignInclusion
import Vegas.Pending.PhaseBindingOpeningRead

/-! # Foreign commitment inclusion from actual counted phase histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- Every actually admitted foreign commitment can be replayed from its
counted history, with its possibly failed typed result unchanged. Fixed-handle
provenance and the static owner/node conditions follow from that history. -/
theorem counted_foreign_binding_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
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
    (foreign : message.sender ≠ owner)
    (includable : original.application.current.native.publicView.BindingIncludable runtime
      ⟨message.id, .commitment event candidate⟩)
    (admitted : (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) = true)
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
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
    scheduler trace
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
      have sender : message.id.1 = actor := by
        have same : actor = message.sender := by
          simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq, Message.sender]
            using bindingOwned
        exact same.symm
      have owned : candidate.1 = actor := candidateOwned.trans sender
      have different : actor ≠ owner := by rwa [← sender]
      simp only [PublicView.BindingIncludable, node] at includable
      change original.application.current.native.publicView.EventReady event ∧
        original.application.current.native.WithinDeadline runtime event ∧ _ at includable
      obtain ⟨publicReady, timely, conditions⟩ := includable
      have ready := (original.application.current.native.publicView_eventReady event).mp publicReady
      change message.id.1 = actor ∧ candidate.1 = actor ∧
        original.application.current.native.accepted (.inr event) = none ∧
          original.application.current.native.HandleUnused candidate at conditions
      obtain ⟨_, _, vacant, unused⟩ := conditions
      have count := PhaseCount.countRecall_history runtime leaks rawTrace
      have output : message ∈ (phaseApplication runtime leaks).outputs (original.recall actor) := by
        rw [← count.1 actor]
        exact List.mem_filter.mpr ⟨member, by simp only [Message.sender, sender, decide_true]⟩
      have signed := phaseOwnCommitmentsFixed_history runtime leaks initial horizon scheduler
        rawTrace
      change PhaseOwnCommitmentsFixed runtime leaks original at signed
      have fixed : original.application.current.native.candidates.lookup candidate ≠ .fresh := by
        have handleEq : candidate = (actor, candidate.2) := Prod.ext owned rfl
        rw [handleEq]
        exact signed actor message output event candidate.2 (by rwa [← handleEq])
      exact frame.foreign_binding_inclusion onlyBindings message.id message found event candidate
        actor different payload outputEq codeEq node ready timely sender owned vacant unused fixed
        none packet admitted clear

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
