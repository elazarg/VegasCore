/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryFirstActivation
import Vegas.Game.OnePacketCanonicalSafety
import Vegas.Game.RecoveryProtectedCalls
import Vegas.Pending.ExclusionAcceptedOutput
import Vegas.Game.OnePacketEventSuccess
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Canonical first responses remain successful through the first exclusion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A canonical fresh first response cannot acquire a failed output in the
scheduler move from the last clear prefix. Only actual recovery service is used. -/
theorem recovery_firstActivation_canonical_succeeds_environment
    (bounds : MessageBounds (graph setup))
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
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup runtime leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup runtime leaks).Submission)
    (submits : (runtime.canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who) event action).transmission = some
        material)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (after : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace
      (some ⟨remaining, none, execution.respond (application setup runtime leaks) who
        (runtime.canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup runtime leaks) who) event action)⟩))
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
    (isPrefix : TracePrefix after target) :
    (event ∈ next.application.config.cut.completed →
      OutputSucceeded next.application.config.store event) ∧
      ¬ next.application.PublicFailure event := by
  let nativeScheduler := RecoveryProjection.nativeScheduler runtime leaks scheduler
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon nativeScheduler trace
  have fits := recovery_firstActivation_inclusionFits (runtime := runtime) initialized nativeLaw
    opportunity
    timely rawTrace rfl clear event turn never
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have settles := recovery_settlesFreshCalls_environment setup leaks initialized nativeLaw
    inclusion who event owned priorRemaining priorExecution prior priorClear command next reached
  exact canonical_firstResponse_succeeds_of_settles (runtime := runtime) bounds horizon
    nativeScheduler bound trace
    event turn fits action material submits bindSuccess after control target isPrefix next
    nextExecution settles

end Vegas
