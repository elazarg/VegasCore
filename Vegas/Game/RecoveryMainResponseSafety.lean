/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDebtFreeResponse
import Vegas.Game.RecoveryCanonicalSafety
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
    (clear : PublicExclusionRecord (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
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
    (priorClear : PublicExclusionRecord
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
  intro supported
  obtain ⟨point, decoded, intended⟩ :=
    intended_of_clear_regular_notOwes wellFormed source focal trace clear regular notOwed
  have forced : ForcedState setup leaks who (some ⟨remaining, some who, execution⟩) :=
    (forcedState_iff_decodedPoint _).mpr
      ⟨point, decoded, forcedPoint_of_intended who intended⟩
  have responderNotOwed : ∀ found, decodedPoint setup execution.application.config = some found →
      ¬ ProtocolState.OwesFailure who setup.program found := by
    intro found foundDecoded
    have same := Option.some.inj (decoded.symm.trans foundDecoded)
    subst found
    exact ProtocolState.Intended.not_owesFailure who setup.program point intended
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  have turn := (pendingEvent_spec pending).1
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  have fits := recovery_firstActivation_inclusionFits initialized nativeLaw opportunity timely
    rawTrace rfl clear event turn never
  obtain ⟨action, material, chosen, submits, bindSuccess⟩ :=
    honestChoice_canonical_of_debtFree wellFormed covers capacity source trace who forced
      responderNotOwed event pending bound fits choice supported
  have sameResponse := Option.some.inj (selected.symm.trans chosen)
  subst response
  have safe := recovery_firstActivation_canonical_succeeds_environment bounds initialized nativeLaw
    opportunity inclusion timely trace clear event turn never action material submits bindSuccess
    after priorRemaining priorExecution prior priorClear command next reached control nextExecution
    target isPrefix
  exact safe.2 failed

end Vegas
