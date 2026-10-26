/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForeignFreshness
import Vegas.Game.OnePacketForeignActivation
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
  {runtime : EventGraphRuntime (graph setup)}
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
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (start control : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (idle : control.actor = none) (owned : (graph setup).actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ control.execution.application.clock - entered) :
    ∃ (before : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some before))
      (response : (application setup runtime leaks).Action)
      (joint : Player → Option (application setup runtime leaks).Action)
      (legal : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Legal
          (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup runtime leaks) owner response⟩ ∈
        ((onePacketProtocol setup runtime leaks bounds horizon
          (RecoveryProjection.nativeScheduler runtime leaks scheduler)).step
            (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) trace ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup runtime leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup runtime leaks) owner)) = some event ∧
      ∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup runtime leaks owner event previous := by
  let nativeScheduler := RecoveryProjection.nativeScheduler runtime leaks scheduler
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  have mappedTrace : ((application setup runtime leaks).protocol (initial.map RecoveryState.native)
      horizon nativeScheduler).Trace (some control) := by
    rw [nativeLaw]
    exact rawTrace
  have actual := Recovery.Opportunity.clear_native runtime leaks initialized opportunity
    control mappedTrace clear
  exact foreign_firstActivation_prefix_of_due (runtime := runtime) wellFormed source focal owner
    different timely start
    control startTrace trace actual startPrefix current event turn clear regular notOwed idle owned
    ready entered activated due

end Vegas
