/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalReplayScan
import Vegas.Game.PhaseProposalReplayPath

/-! # Every consumed publication rank has its actual annotated source step -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem native_replay_event_at_rank
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (generation : Nat) (before : CommitRecoveryState setup.program)
    {after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace (some before))
    (trace : setup.commitRecoveryProtocol.Trace after)
    (extension : NativeSourceReplayExtension setup native generation prior trace)
    (inherited : Finset Player)
    (initialScan : before.excluded = inherited ∪ native.failureOwnersBefore
      (instructionCount setup.program - ProtocolState.remaining setup.program before.point))
    (rank : Nat)
    (lower : instructionCount setup.program -
      ProtocolState.remaining setup.program before.point ≤ rank)
    (upper : rank < instructionCount setup.program -
      ProtocolState.remaining setup.program before.point + (trace.length - prior.length)) :
    ∃ (event : setup.commitRecoveryProtocol.StepEvent)
      (state : CommitRecoveryState setup.program),
      event ∈ (proposalSourceSteps setup trace).drop prior.length ∧ event.source = some state ∧
      state.generation = generation ∧
      rank = instructionCount setup.program - ProtocolState.remaining setup.program state.point ∧
      ProtocolState.atCommit setup.program state.point = false ∧
      NativeProposalReadback native 0 setup.program state.point ∧
      NativeDisclosureReadback native 0 setup.program state.point state.excluded event.joint ∧
      state.excluded = inherited ∪ native.failureOwnersBefore rank := by
  obtain ⟨events, points, chain, head, steps, annotated, length, cursors⟩ := extension
  let index := rank - (instructionCount setup.program -
    ProtocolState.remaining setup.program before.point)
  have bound : index < events.length := by omega
  let event := events[index]'bound
  have member : event ∈ events := List.getElem_mem bound
  obtain ⟨first, last, source, _target, moved, disclosure, firstMember⟩ := annotated event member
  have cursor := cursors index bound
  rw [source] at cursor
  simp only [Option.map_some, CommitRecoveryState.atPoint] at cursor
  have currentRank := Option.some.inj cursor
  cases points with
  | nil => cases head
  | cons start rest =>
      have initialEq : CommitRecoveryState.atPoint start.1 start.2 generation = before :=
        Option.some.inj head
      have pointEq := congrArg CommitRecoveryState.point initialEq
      have excludedEq := congrArg CommitRecoveryState.excluded initialEq
      change start.1 = before.point at pointEq
      change start.2 = before.excluded at excludedEq
      have startScan : start.2 = inherited ∪ native.failureOwnersBefore
          (instructionCount setup.program - ProtocolState.remaining setup.program start.1) := by
        rw [pointEq, excludedEq]
        exact initialScan
      have scan := native_public_path_point_scan setup mode native inherited start rest chain
        startScan first firstMember
      refine ⟨event, CommitRecoveryState.atPoint first.1 first.2 generation, ?_, source, rfl,
        ?_, moved.1.2.1, moved.2.2.1, disclosure, ?_⟩
      · rw [steps]
        rw [← proposalSourceSteps_length setup prior, List.drop_left]
        exact member
      · dsimp only [CommitRecoveryState.atPoint]
        dsimp only [index] at currentRank
        omega
      · dsimp only [CommitRecoveryState.atPoint]
        have same : rank = instructionCount setup.program -
            ProtocolState.remaining setup.program first.1 := by
          dsimp only [index] at currentRank
          omega
        simpa only [same] using scan

end Vegas
