/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalSampleHistory
import Vegas.Game.ProposalRecoveryPerturbation

/-! # The selected Nature checkpoint and its full enriched source history -/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [Fintype Player] in
private theorem ownerless_prefix_history_eq {E : ExecutionProtocol Player}
    (first left right : E.History)
    (inactive : ∀ who, ¬ E.active first.state who)
    (leftPrefix : TracePrefix first.trace left.trace)
    (rightPrefix : TracePrefix first.trace right.trace)
    (leftLength : left.trace.length = first.trace.length + 1)
    (rightLength : right.trace.length = first.trace.length + 1)
    (same : left.state = right.state) : left = right := by
  classical
  rcases first with ⟨start, past⟩
  rcases left with ⟨leftState, leftTrace⟩
  rcases right with ⟨rightState, rightTrace⟩
  change leftState = rightState at same
  subst rightState
  cases leftTrace with
  | start =>
      have bounded := leftPrefix.length_le
      simp only [Trace.length] at leftLength bounded
      omega
  | extend =>
    cases leftPrefix with
    | refl =>
      omega
    | @extend source target prior earlier joint legal realized =>
      rename_i source prior joint _actualLegal _actualRealized
      have priorLength : past.length = prior.length := by
        change prior.length + 1 = past.length + 1 at leftLength
        omega
      have priorEq := earlier.eq_of_length priorLength
      have sourceEq : start = source := congrArg History.state priorEq
      subst source
      have traceEq : past = prior := by
        simpa only [History.mk.injEq, heq_eq_eq, true_and] using priorEq
      subst prior
      cases rightTrace with
      | start =>
          have bounded := rightPrefix.length_le
          simp only [Trace.length] at rightLength bounded
          omega
      | extend =>
        cases rightPrefix with
        | refl =>
          omega
        | @extend otherSource otherTarget otherPrior before otherJoint otherLegal otherRealized =>
          rename_i otherSource otherPrior otherJoint _otherActualLegal _otherActualRealized
          have otherLength : past.length = otherPrior.length := by
            change otherPrior.length + 1 = past.length + 1 at rightLength
            omega
          have otherEq := before.eq_of_length otherLength
          have otherSourceEq : start = otherSource := congrArg History.state otherEq
          subst otherSource
          have otherTraceEq : past = otherPrior := by
            simpa only [History.mk.injEq, heq_eq_eq, true_and] using otherEq
          subst otherPrior
          have empty : joint = fun _ => none := by
            funext who
            exact LegalOption.eq_none_of_inactive _ (E.legalOption_of_legal legal who)
              (inactive who)
          have otherEmpty : otherJoint = fun _ => none := by
            funext who
            exact LegalOption.eq_none_of_inactive _ (E.legalOption_of_legal otherLegal who)
              (inactive who)
          cases empty.trans otherEmpty.symm
          rfl

/-- At the actual singleton Nature phase, a supported enriched source step
with the selected checkpoint's typed target is its literal full lifted trace. -/
theorem RecoverySourceCheckpoint.sample_history_eq_of_target
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (frontier : state.Frontier)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .sample)
    (next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    {fuel : Nat} (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (history : setup.proposalRecoveryProtocol.History)
    (supported : history ∈ (setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
      1 ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩).support)
    (target : history.state = some (CommitRecoveryState.atPoint
      (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
        (phase.drain state.current).excluded state.generation)) :
    history = ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ := by
  let before := CommitRecoveryState.atPoint
    (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
      state.entry.excluded state.generation
  let after := CommitRecoveryState.atPoint
    (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
      (phase.drain state.current).excluded state.generation
  have firstRank := checkpoint.saved_position
  have lastRank := next.saved_position
  have low : state.attempt.phase = phase.low := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have boundary : phase.high = PhaseRuntimeState.phaseLow remaining := by
    have adjacent := frontier.adjacent
    have last := frontier.last
    rw [installed] at adjacent last
    cases remaining with
    | nil => exact last phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
    | cons following rest => exact adjacent.rel_head? (y := following) (by simp)
  change instructionCount setup.program - ProtocolState.remaining setup.program before.point =
    state.attempt.phase at firstRank
  change instructionCount setup.program - ProtocolState.remaining setup.program after.point =
    PhaseRuntimeState.phaseLow remaining at lastRank
  have boundedBefore := ProtocolState.remaining_le_instructionCount setup.program before.point
  have boundedAfter := ProtocolState.remaining_le_instructionCount setup.program after.point
  have singleton := phase.sample_singleton kind
  have counted := setup.commitRecovery_same_generation_length path before after rfl rfl rfl
  change ProtocolState.remaining setup.program after.point + next.trace.length =
    ProtocolState.remaining setup.program before.point + checkpoint.trace.length at counted
  have nextLength : next.trace.length = checkpoint.trace.length + 1 := by omega
  have reached := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin _ 1 _ history
    supported
  have kept := reached.tracePrefix
  have semanticKept := setup.proposalRecoveryEraseTrace_prefix kept
  have sourceCount := setup.commitRecovery_same_generation_length semanticKept.reachesWithin
    before after rfl target rfl
  simp only [proposalRecoveryEraseTrace_length, proposalRecoveryEraseTrace_lift] at sourceCount
  have sourceLength : history.trace.length = checkpoint.trace.length + 1 := by omega
  have positive : state.attempt.phase < instructionCount setup.program := by
    have high := phase.bounded
    change phase.high ≤ eventCount setup.program at high
    have nonempty := phase.nonempty
    rw [eventCount_eq_instructionCount] at high
    omega
  let event : (serviceGraph setup mode).EventId := ⟨state.attempt.phase, by
    change state.attempt.phase < eventCount setup.program
    rwa [eventCount_eq_instructionCount]⟩
  have inside : event ∈ phase.events := (phase.mem_events event).mpr
    ⟨low.ge, by have nonempty := phase.nonempty; change state.attempt.phase < phase.high; omega⟩
  have typed := phase.fields event ((phase.mem_events event).mp inside).1
    ((phase.mem_events event).mp inside).2
  rw [kind] at typed
  obtain ⟨payload, output⟩ := typed
  have actorless : (serviceGraph setup mode).actor? event = none := by
    cases viewed : nodeView (serviceGraph setup mode) event with
    | sample actual law outputEq codeEq =>
        exact (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
    | bind owner actual outputEq codeEq => cases outputEq.symm.trans output
    | resolve owner actual binding checks outputEq codeEq => cases outputEq.symm.trans output
  have sourceActor : ProtocolState.actor setup.program before.point = none :=
    (source_actor_at_compiled_rank setup.program mode before.point event firstRank.symm).trans
      actorless
  have inactive : ∀ who, ¬ setup.proposalRecoveryProtocol.active (some before) who := by
    intro who active
    change ProtocolState.actor setup.program before.point = some who ∧ who ∉ before.excluded
      at active
    rw [sourceActor] at active
    cases active.1
  apply ownerless_prefix_history_eq
    ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩ history
      ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ inactive kept
        (setup.proposalRecoveryLiftTrace_prefix labels path.tracePrefix)
  · simpa only [proposalRecoveryLiftTrace_length] using sourceLength
  · simpa only [proposalRecoveryLiftTrace_length] using nextLength
  · exact target

end Vegas
