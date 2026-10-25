/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFirstActivation
import Vegas.Game.OnePacketEventSuccess
import Vegas.Pending.ExclusionAcceptedOutput
import Vegas.Game.SourceServiceAsyncTimeliness
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Canonical counted response success from native timing and settlement facts

The accepted-output argument uses a fresh callback's original deadline guard
and the existing signed-call settlement invariant. How a concrete service
supplies those facts is independent of this proof over actual counted histories.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- An actual canonical counted response succeeds at an actual later counted
endpoint when its native deadline and protected-call settlement facts hold. -/
theorem canonical_firstResponse_succeeds_of_settles
    (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission = some material)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (after : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none,
        execution.respond (application setup leaks) who
          ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event action)⟩))
    (control : (application setup leaks).Control)
    (target : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (isPrefix : TracePrefix after target)
    (next : (application setup leaks).Execution) (nextExecution : control.execution = next)
    (settles : SettlesFreshCalls setup leaks who event bound next) :
    (event ∈ next.application.config.cut.completed →
      OutputSucceeded next.application.config.store event) ∧
      ¬ next.application.PublicFailure event := by
  have invariant := acceptanceInvariant_respond bounds horizon scheduler trace event turn
    action material submits bindSuccess after
  have transports : ∀ {state}
      {later : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
        scheduler).Trace state}, TracePrefix after later →
      AcceptanceInvariant setup leaks bounds horizon scheduler who
        (respondEntry setup leaks execution who ((runtime setup).canonicalServiceDecision leaks who
          (execution.recall who) (execution.observe (application setup leaks) who) event action))
        (sentEnvelope setup leaks execution who material) event execution.application.config
        state := by
    intro state later earlier
    induction earlier with
    | refl => exact invariant
    | extend previous joint legal realized ih =>
        exact acceptanceInvariant_transition bounds horizon scheduler who _ _ event _
          _ _ joint legal ih realized
  have finalInvariant := transports isPrefix
  obtain ⟨_, records, _emitted, _, _, _, accepted⟩ := finalInvariant
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have call := canonical_freshCall rawTrace bound who event turn fits action material submits
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  obtain ⟨earlier, later, split⟩ := records
  have member : (sentEnvelope setup leaks execution who material) ∈
      (application setup leaks).outputs (control.execution.recall who) :=
    List.mem_filterMap.mpr ⟨respondEntry setup leaks execution who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action),
      by rw [split]; simp, _emitted⟩
  rw [respondEntry_of_transmission execution who _ material submits] at split
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (runtime setup) leaks other event
        (sentEnvelope setup leaks execution who material).id := by
    intro other present
    exact onePacket_not_emitsOtherFor bounds target who event _ member call.addressed other
      (by
        rw [split]
        rcases List.mem_append.mp present with first | last
        · exact List.mem_append_left _ first
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ last))
  rw [nextExecution] at split
  have succeeds (completed : event ∈ next.application.config.cut.completed) :
      OutputSucceeded next.application.config.store event := by
    have receipt := (settles earlier _ later _ split call sole).1 completed
    rw [← nextExecution] at receipt
    rw [← nextExecution]
    exact accepted receipt
  have rawTarget := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler target
  have binding := (legalFacts setup leaks horizon scheduler control rawTarget).binding
  rw [nextExecution] at binding
  exact ⟨succeeds, fun failed => (succeeds failed.completed).not_publicFailure binding failed⟩


end Vegas
