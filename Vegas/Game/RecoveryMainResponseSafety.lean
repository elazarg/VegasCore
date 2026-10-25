/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDebtFreeResponse
import Vegas.Game.RecoveryCanonicalSafety
import Vegas.Game.OnePacketMainResponseSafety
import Vegas.Game.OnePacketClearRegularity

/-! # First public event failures exclude source-main response support -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A first event failure cannot follow a source-main response at its earlier
actual debt-free first activation. Actual canonical transmission and menu
admission are derived, including the opening guard condition. -/
theorem recovery_firstActivation_not_main_of_publicFailure
    (bounds : MessageBounds (graph setup)) (wellFormed : setup.WellFormed)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
      (some ⟨remaining, some who, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Choice who
      (some (execution.recall who, execution.observe (application setup leaks) who)))
    (response : (application setup leaks).Action) (selected : choice.1 = some response)
    (after : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩))
    (priorRemaining : Nat) (priorExecution : (application setup leaks).Execution)
    (prior : ((application setup leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
      (some ⟨priorRemaining + 1, none, priorExecution⟩))
    (priorClear : ExclusionEvidence 0 ∅
      (⟨priorExecution.application, ∅⟩ : RecoveryState (graph setup)))
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (priorExecution.environmentStep (application setup leaks) command).support)
    (control : (application setup leaks).Control) (nextExecution : control.execution = next)
    (target : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some control))
    (isPrefix : TracePrefix after target)
    (failed : next.application.PublicFailure event) :
    choice ∉ (honestChoice setup leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source who
      (some (execution.recall who, execution.observe (application setup leaks) who))).support := by
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  have fits := recovery_firstActivation_inclusionFits initialized nativeLaw opportunity timely
    rawTrace rfl clear event (pendingEvent_spec pending).1 never
  have owned := (pendingEvent_spec pending).2.2.1
  have settles := recovery_settlesFreshCalls_environment setup leaks initialized nativeLaw inclusion
    who event owned priorRemaining priorExecution prior priorClear command next reached
  exact firstResponse_not_main_of_publicFailure_of_settles bounds wellFormed covers capacity source
    focal horizon nativeScheduler bound trace clear regular notOwed event pending fits choice
    response selected after next settles control nextExecution target isPrefix failed

end Vegas
