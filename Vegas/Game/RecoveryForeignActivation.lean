/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForeignFreshness
import Vegas.Game.OnePacketClearRegularity
import Vegas.Pending.ReactiveOwnerActivationRecall

/-! # Actual future foreign first activations before a clear deadline -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- A due foreign event at a clear regular endpoint before focal debt has an
actual first owner response after an earlier focal source turn. The witness
retains the full supported transition and first-activation recall. -/
theorem recovery_foreign_firstActivation_prefix_of_due
    (wellFormed : setup.WellFormed)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start control : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : PublicExclusionRecord
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (idle : control.actor = none) (owned : (graph setup).actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ control.execution.application.clock - entered) :
    ∃ (before : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon
        (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some before))
      (response : (application setup leaks).Action)
      (joint : Player → Option (application setup leaks).Action)
      (legal : (onePacketProtocol setup leaks bounds horizon
        (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Legal
          (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup leaks) owner response⟩ ∈
        ((onePacketProtocol setup leaks bounds horizon
          (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).step
            (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) trace ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) = some event ∧
      ∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup leaks owner event previous := by
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  have mappedTrace : ((application setup leaks).protocol (initial.map RecoveryState.native)
      horizon nativeScheduler).Trace (some control) := by
    rw [nativeLaw]
    exact rawTrace
  obtain ⟨entry, remembered, atTurn⟩ := Recovery.due_owner_recalled_turn_clear_native
    (runtime setup) leaks initialized opportunity timely
    (serviceGraph_revealRelaxedOrdered setup .sequential) control mappedTrace idle clear event owner
    owned ready entered activated due
  have occurs : ∃ entry ∈ control.execution.recall owner,
      ActivatedAt setup leaks owner event entry := ⟨entry, remembered, atTurn⟩
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal trace clear regular notOwed
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    (bounds.onePacketMenu (runtime setup) leaks) horizon nativeScheduler trace control rfl
  have samePoint := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  subst point
  have submissions := onePacket_ownSubmissionsAtTurn bounds trace residual.checkpoint.ordered _
    residual.decode intended owner
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

end Vegas
