/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCountedInclusion
import Vegas.Pending.PhaseBindingCountedOpening
import Vegas.Pending.ReactiveCountedSurvivor

/-! # All authentic counted inclusion cases in a clear phased repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- The actual original counted packet determines every inclusion case.
Native readiness, timeliness, successful-opening provenance and image
exclusion are derived on the accepting branch; all other cases reject jointly.
The submitted-binding record is carried by the response induction. -/
theorem counted_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (recorded : memory.RecordsSubmittedBindings runtime (nativeLeaks (graph := graph)) owner
      (execution runtime leaks original) (execution runtime leaks repaired))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat) (actorTurn : Option Player)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, actorTurn, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, actorTurn, repaired⟩))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ original.network.inputs)
    (found : original.network.lookup message.id = some message)
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
  have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
    scheduler left
  have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (physical.clean.2 message member)
  have correct := permitted.2.1
  cases call : message.payload.packet.call with
  | commitment event candidate =>
      exact frame.counted_binding_inclusion onlyBindings recorded bounds plan inputs horizon
        scheduler remaining actorTurn left message member found event candidate call clear
  | malformed raw =>
      simp only [CountCallCorrect, PhaseCount.nativeMessage, call] at correct
  | opening event candidate raw =>
      by_cases admitted : (message.payload.tokenValid original.application.attempt &&
          original.application.allows message.payload.packet.call &&
          !original.application.current.excludedCall message.payload.packet.call) = true
      · by_cases ready : original.application.current.native.config.cut.Ready event
        · by_cases timely : original.application.current.native.WithinDeadline runtime event
          · have current : message.payload.attempt = original.application.attempt :=
              of_decide_eq_true (Bool.and_eq_true_iff.mp
                (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).1).1
            have allowed : original.application.allows message.payload.packet.call = true :=
              (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp admitted).1).2
            obtain ⟨phase, installed, named, namedEq, inside⟩ :=
              original.application.allows_event message.payload.packet.call allowed
            have sameEvent : named = event := by
              have same := namedEq
              rw [call] at same
              exact Option.some.inj same.symm
            subst named
            have acting : graph.actor? event = some message.sender :=
              countCallCorrect_owned_event _ (PhaseCount.nativeMessage message) correct (by
                simp only [PhaseCount.nativeMessage, call, Payload.event?])
            have request : original.application.SeedRequest message.sender
                ⟨message.payload.attempt, event⟩ := by
              refine ⟨current, ⟨phase, installed, inside⟩, ready, acting, ?_⟩
              rw [frame.clearOriginal]
              simp
            have resolves := correct
            unfold CountCallCorrect at resolves
            dsimp only [PhaseCount.nativeMessage] at resolves
            rw [call] at resolves
            cases node : nodeView graph event with
            | bind actor payload outputEq codeEq => simp only [node, and_false] at resolves
            | sample payload law outputEq codeEq => simp only [node, and_false] at resolves
            | resolve actor payload binding checks outputEq codeEq =>
                exact frame.counted_opening_inclusion onlyBindings bounds plan inputs horizon
                  scheduler remaining actorTurn left right message member found event candidate raw
                  call request actor payload binding checks outputEq codeEq node timely clear
          · exact frame.opening_late message.id message found event candidate raw call timely
        · exact frame.opening_not_ready message.id message found event candidate raw call ready
      · exact frame.include_unauthorized message.id message found (Bool.eq_false_iff.mpr admitted)

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
