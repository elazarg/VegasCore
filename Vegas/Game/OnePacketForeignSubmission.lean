/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForeignFreshness
import Vegas.Game.OnePacketClearRegularity

/-! # Foreign first activations behind submitted packets -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- A recorded submission for a still-ready foreign event identifies an actual
first owner response after an earlier focal source turn, at a clear regular
endpoint before focal debt. -/
theorem foreign_firstActivation_prefix_of_recorded
    (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    (start control : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some start))
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : PublicExclusionRecord
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall owner) event = true) :
    ∃ (before : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some before))
      (response : (application setup leaks).Action)
      (joint : Player → Option (application setup leaks).Action)
      (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup leaks) owner response⟩ ∈
        ((onePacketProtocol setup leaks bounds horizon scheduler).step
          (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) trace ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) = some event ∧
      ∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup leaks owner event previous := by
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal trace clear regular notOwed
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
  have samePoint := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  subst point
  have submissions := onePacket_ownSubmissionsAtTurn bounds trace residual.checkpoint.ordered _
    residual.decode intended owner
  obtain ⟨entry, remembered, submitted⟩ :=
    ((runtime setup).eventRecorded_iff leaks (control.execution.recall owner) event).mp recorded
  have occurs : ∃ entry ∈ control.execution.recall owner,
      ActivatedAt setup leaks owner event entry :=
    ⟨entry, remembered, submissions entry remembered event submitted⟩
  obtain ⟨before, prior, response, joint, legal, realized, isPrefix, acting, chosen, pending,
    never⟩ := firstActivation_response_prefix_of_recall trace owner event occurs submissions
  have unfinished : event ∉ start.execution.application.config.cut.completed := by
    intro completed
    obtain ⟨value, output⟩ := Option.isSome_iff_exists.mp
      ((start.execution.application.config.output_available event).mpr completed)
    have stored : start.execution.application.config.store (.inr event) = some value := output
    have retained := storedValue_of_tracePrefix startTrace startPrefix (.inr event) value stored
    change control.execution.application.config.outputs event = some value at retained
    exact ready.1 ((control.execution.application.config.output_available event).mp
      (by rw [retained]; rfl))
  have beforePrefix : TracePrefix prior trace :=
    (TracePrefix.extend .refl joint legal realized).trans isPrefix
  have readyBefore := (before.execution.application.publicView_eventReady event).mp
    (pendingEvent_spec pending).2.1
  have future := foreign_ready_prefix_after_ownTurn startTrace prior startPrefix beforePrefix focal
    owner different current event turn owned unfinished readyBefore
  exact ⟨before, prior, response, joint, legal, realized, future, isPrefix, acting, chosen, pending,
    never⟩

/-- A pending authentic envelope names a submission already retained in its
sender's recall. It can therefore be attributed before an inclusion attempt. -/
theorem eventRecorded_of_pending
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (owner : Player) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (member : message ∈ control.execution.network.pending)
    (sender : message.sender = owner)
    (named : message.payload.call.event? (graph setup) = some event) :
    (runtime setup).eventRecorded leaks (control.execution.recall owner) event = true := by
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have signed := signedCommitments_history (runtime setup) leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  obtain ⟨entry, remembered, material, transmitted, emitted, _⟩ :=
    signed.provenance.pending message member
  rw [sender] at remembered
  obtain ⟨_, actual, sent, call⟩ := signed.emissions owner entry remembered message emitted
  apply ((runtime setup).eventRecorded_iff leaks (control.execution.recall owner) event).mpr
  refine ⟨entry, remembered, ?_⟩
  unfold EventGraphRuntime.submittedEvent?
  rw [sent]
  change actual.call.packet.event? (graph setup) = some event
  rw [← call]
  exact named

end Vegas
