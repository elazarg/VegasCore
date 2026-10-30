/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.SourceServiceFreshCall
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Exact canonical response results under native settlement

A settled canonical response retains the action and typed result certified at submission.
The result may be failure; guards are evaluated by the native handler.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A settled canonical response writes exactly its certified action and typed result. -/
theorem canonical_firstResponse_result_of_settles
    (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat)
    {remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (fits : execution.application.publicView.InclusionFitsDeadline runtime bound event)
    (action : (graph setup).Action event) (material : (application setup runtime leaks).Submission)
    (submits : (runtime.canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who) event action).transmission = some
        material)
    (after : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none,
        execution.respond (application setup runtime leaks) who
          (runtime.canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup runtime leaks) who) event action)⟩))
    (control : (application setup runtime leaks).Control)
    (target : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control)) (isPrefix : TracePrefix after target)
    (next : (application setup runtime leaks).Execution) (nextExecution : control.execution = next)
    (settles : SettlesFreshCalls setup leaks who event bound next) :
    ∃ output, AcceptanceWitness event (sentEnvelope setup runtime leaks execution who material)
      execution.application.config action output next.application ∧
      (event ∈ next.application.config.cut.completed →
        next.application.config.outputs event = some output ∧
          ∃ defaultEvent, (⟨event, some action, defaultEvent⟩ : (graph setup).Completion) ∈
            next.application.config.history) := by
  obtain ⟨output, invariant⟩ := acceptanceInvariant_respond (runtime := runtime) bounds horizon
    scheduler trace event turn action material submits after
  have transports : ∀ {state}
      {later : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace state}, TracePrefix after later →
      AcceptanceInvariant setup runtime leaks bounds horizon scheduler who
        (respondEntry setup runtime leaks execution who (runtime.canonicalServiceDecision leaks who
          (execution.recall who) (execution.observe (application setup runtime leaks) who) event
            action))
        (sentEnvelope setup runtime leaks execution who material) event execution.application.config
        action output state := by
    intro state later earlier
    induction earlier with
    | refl => exact invariant
    | extend previous joint legal realized ih =>
        exact acceptanceInvariant_transition (runtime := runtime) bounds horizon scheduler who _ _
          event _ action output _ _ joint legal ih realized
  have finalInvariant := transports isPrefix
  obtain ⟨_, records, _emitted, _, finalWitness, _, accepted⟩ := finalInvariant
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have call := canonical_freshCall rawTrace bound who event turn fits action material submits
  obtain ⟨earlier, later, split⟩ := records
  have member : (sentEnvelope setup runtime leaks execution who material) ∈
      (application setup runtime leaks).outputs (control.execution.recall who) :=
    List.mem_filterMap.mpr ⟨respondEntry setup runtime leaks execution who
      (runtime.canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup runtime leaks) who) event action),
      by rw [split]; simp, _emitted⟩
  rw [respondEntry_of_transmission (runtime := runtime) execution who _ material submits] at split
  have sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor runtime leaks other event
        (sentEnvelope setup runtime leaks execution who material).id := by
    intro other present
    exact onePacket_not_emitsOtherFor (runtime := runtime) bounds target who event _ member
      call.addressed other
      (by
        rw [split]
        rcases List.mem_append.mp present with first | last
        · exact List.mem_append_left _ first
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ last))
  rw [nextExecution] at split finalWitness
  refine ⟨output, finalWitness, ?_⟩
  intro completed
  have receipt := (settles earlier _ later _ split call sole).1 completed
  rw [← nextExecution] at receipt ⊢
  exact accepted receipt


end Vegas
