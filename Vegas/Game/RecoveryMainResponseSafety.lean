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
  {runtime : EventGraphRuntime (graph setup)}
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
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
      (some ⟨remaining, some who, execution⟩))
    (clear : ExclusionEvidence 0 ∅ (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup runtime leaks who (some (execution.recall who,
      execution.observe (application setup runtime leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup runtime leaks who event entry)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Choice who
      (some (execution.recall who, execution.observe (application setup runtime leaks) who)))
    (response : (application setup runtime leaks).Action) (selected : choice.1 = some response)
    (after : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
      (some ⟨remaining, none, execution.respond (application setup runtime leaks) who response⟩))
    (priorRemaining : Nat) (priorExecution : (application setup runtime leaks).Execution)
    (prior : ((application setup runtime leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
      (some ⟨priorRemaining + 1, none, priorExecution⟩))
    (priorClear : ExclusionEvidence 0 ∅
      (⟨priorExecution.application, ∅⟩ : RecoveryState (graph setup)))
    (command : (application setup runtime leaks).Command) (next : (application setup runtime
      leaks).Execution)
    (reached : next ∈ (priorExecution.environmentStep (application setup runtime leaks)
      command).support)
    (control : (application setup runtime leaks).Control) (nextExecution : control.execution = next)
    (target : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (isPrefix : TracePrefix after target)
    (failed : next.application.PublicFailure event) :
    choice ∉ (honestChoice setup runtime leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source who
      (some (execution.recall who, execution.observe (application setup runtime leaks)
        who))).support := by
  let nativeScheduler := RecoveryProjection.nativeScheduler runtime leaks scheduler
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  have fits := recovery_firstActivation_inclusionFits (runtime := runtime) initialized nativeLaw
    opportunity timely
    rawTrace rfl clear event (pendingEvent_spec (runtime := runtime) pending).1 never
  have owned := (pendingEvent_spec (runtime := runtime) pending).2.2.1
  have settles := recovery_settlesFreshCalls_environment setup leaks initialized nativeLaw inclusion
    who event owned priorRemaining priorExecution prior priorClear command next reached
  exact firstResponse_not_main_of_publicFailure_of_settles (runtime := runtime) bounds wellFormed
    covers capacity source
    focal horizon nativeScheduler bound trace clear regular notOwed event pending fits choice
    response selected after next settles control nextExecution target isPrefix failed

end Vegas
