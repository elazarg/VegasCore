/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForeignFailure
import Vegas.Game.RecoveryForeignActivation
import Vegas.Game.OnePacketForeignSubmission
import Vegas.Game.OnePacketCompletionOrigin
import Vegas.Game.OnePacketFilteredPrefix
import Vegas.Game.RecoveryMainResponseSafety

/-! # First foreign failures identify a future non-main response -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- A first foreign public failure before focal debt remembers an actual
non-main foreign first response after the comparison's focal source turn.
Both expiry and consumed opening traffic are attributed from actual execution. -/
theorem recovery_foreign_nonmain_prefix_of_firstFailure
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (target : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
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
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) target ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup leaks) owner)) = some event ∧
      (∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup leaks owner event previous) ∧
      responseChoice setup leaks bounds (initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup leaks) owner)) response ∉
        (honestChoice setup leaks bounds (initialLaw setup) horizon
          (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source owner
          (some (before.execution.recall owner,
            before.execution.observe (application setup leaks) owner))).support := by
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  have nativeOpportunity (current : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon nativeScheduler).Trace (some current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt (runtime setup) leaks current.execution delay := by
    have actual := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native (runtime setup) leaks initialized opportunity current
      actual clear
  have nativeInclusion (current : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon nativeScheduler).Trace (some current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      ProtectedInclusionAt (runtime setup) leaks current.execution bound := by
    have actual := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.ProtectedInclusion.clear_native (runtime setup) leaks initialized inclusion
      current actual clear
  exact foreign_nonmain_prefix_of_firstFailure wellFormed covers capacity source focal owner
    different nativeOpportunity nativeInclusion timely start startTrace remaining execution trace
    startPrefix current event turn clear regular notOwed owned command next reached target
    tracePrefix failed

theorem recovery_firstForeignFailure_not_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : ((runtime setup).recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (start : (application setup leaks).Control)
    (startTrace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace (some start))
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup leaks).Command) (next : (application setup leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (target : (onePacketProtocol setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler)).Trace
        (some ⟨remaining, command.actor? (application setup leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
    ¬ MainActivationTraceAfter setup leaks bounds horizon
      (RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler) source focal
      startTrace.length target := by
  let nativeScheduler := RecoveryProjection.nativeScheduler (runtime setup) leaks scheduler
  have nativeOpportunity (current : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon nativeScheduler).Trace (some current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt (runtime setup) leaks current.execution delay := by
    have actual := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native (runtime setup) leaks initialized opportunity current
      actual clear
  have nativeInclusion (current : (application setup leaks).Control)
      (prior : (onePacketProtocol setup leaks bounds horizon nativeScheduler).Trace (some current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      ProtectedInclusionAt (runtime setup) leaks current.execution bound := by
    have actual := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.ProtectedInclusion.clear_native (runtime setup) leaks initialized inclusion
      current actual clear
  exact firstForeignFailure_not_mainActivationTraceAfter wellFormed covers capacity source
    focal owner different nativeOpportunity nativeInclusion timely start startTrace remaining
    execution trace startPrefix current event turn clear regular notOwed owned command next reached
    target tracePrefix failed

end Vegas
