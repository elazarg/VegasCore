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
  {runtime : EventGraphRuntime (graph setup)}
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
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (start : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some start))
    (remaining : Nat) (execution : (application setup runtime leaks).Execution)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup runtime leaks).Command) (next : (application setup runtime
      leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks) command).support)
    (target : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
        (some ⟨remaining, command.actor? (application setup runtime leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
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
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) target ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup runtime leaks owner (some (before.execution.recall owner,
        before.execution.observe (application setup runtime leaks) owner)) = some event ∧
      (∀ previous ∈ before.execution.recall owner,
        ¬ ActivatedAt setup runtime leaks owner event previous) ∧
      responseChoice setup runtime leaks bounds (initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler) owner
        (some (before.execution.recall owner,
          before.execution.observe (application setup runtime leaks) owner)) response ∉
        (honestChoice setup runtime leaks bounds (initialLaw setup) horizon
          (RecoveryProjection.nativeScheduler runtime leaks scheduler) source owner
          (some (before.execution.recall owner,
            before.execution.observe (application setup runtime leaks) owner))).support := by
  let nativeScheduler := RecoveryProjection.nativeScheduler runtime leaks scheduler
  have nativeOpportunity (current : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon nativeScheduler).Trace (some
        current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks current.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity current
      actual clear
  have nativeInclusion (current : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon nativeScheduler).Trace (some
        current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      ProtectedInclusionAt runtime leaks current.execution bound := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.ProtectedInclusion.clear_native runtime leaks initialized inclusion
      current actual clear
  exact foreign_nonmain_prefix_of_firstFailure (runtime := runtime) wellFormed covers capacity
    source focal owner
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
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (start : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some start))
    (remaining : Nat) (execution : (application setup runtime leaks).Execution)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup runtime leaks).Command) (next : (application setup runtime
      leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks) command).support)
    (target : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
        (some ⟨remaining, command.actor? (application setup runtime leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
    ¬ MainActivationTraceAfter setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      startTrace.length target := by
  let nativeScheduler := RecoveryProjection.nativeScheduler runtime leaks scheduler
  have nativeOpportunity (current : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon nativeScheduler).Trace (some
        current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks current.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity current
      actual clear
  have nativeInclusion (current : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon nativeScheduler).Trace (some
        current))
      (clear : ExclusionEvidence 0 ∅
        (⟨current.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      ProtectedInclusionAt runtime leaks current.execution bound := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon nativeScheduler prior
    rw [← nativeLaw] at actual
    exact Recovery.ProtectedInclusion.clear_native runtime leaks initialized inclusion
      current actual clear
  exact firstForeignFailure_not_mainActivationTraceAfter (runtime := runtime) wellFormed covers
    capacity source
    focal owner different nativeOpportunity nativeInclusion timely start startTrace remaining
    execution trace startPrefix current event turn clear regular notOwed owned command next reached
    target tracePrefix failed

end Vegas
