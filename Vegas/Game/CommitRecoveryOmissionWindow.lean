/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptExit
import Vegas.Game.CommitRecoveryNoMissContinuation

/-! # Original commitment-window laws determined by actual omission kernels

Typed choices may differ at every slot. The actual public omission scan is
enough to compare the original finite runners, and an already failed attempt
then has one erased terminal continuation law.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem one_step_omission_word
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    (setup.commitRecoveryModel.runBehavioralFrom profile 1 history).map
        (fun next => setup.omissionRecall next.trace) =
      ((setup.commitRecoveryModel.behavioralJoint profile history.trace running).map
        (fun draw who => CommitRecoveryMove.missed (draw.val who))).map
          (fun missed => missed :: setup.omissionRecall history.trace) := by
  rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile 0 running,
    PMF.map_bind, PMF.map_comp]
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply congrArg (PMF.bind _)
  funext draw
  apply map_bindOnSupport_const
  intro target supported
  simp only [InformationModel.runBehavioralFrom, runRandomizedFor, PMF.pure_map]
  rfl

/-- Equal actual one-step omission laws propagate through the entire original
commitment window. The hypothesis concerns local raw kernels, not an assumed
stopped law, source endpoint, or refreshed entry distribution. -/
theorem commitRecovery_window_omission_law_eq
    (leftProfile rightProfile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    (matched : ∀ (left right : setup.commitRecoveryProtocol.History)
      (_leftKept : TracePrefix prior left.trace) (_rightKept : TracePrefix prior right.trace)
      (_word : setup.omissionRecall left.trace = setup.omissionRecall right.trace)
      (_inside : left.trace.length + ProtocolState.commitEnd setup.program first.point <
        prior.length + ProtocolState.remaining setup.program first.point)
      (leftRunning : ¬ setup.commitRecoveryProtocol.terminal left.state)
      (rightRunning : ¬ setup.commitRecoveryProtocol.terminal right.state),
      (setup.commitRecoveryModel.behavioralJoint leftProfile left.trace leftRunning).map
          (fun draw who => CommitRecoveryMove.missed (draw.val who)) =
        (setup.commitRecoveryModel.behavioralJoint rightProfile right.trace rightRunning).map
          (fun draw who => CommitRecoveryMove.missed (draw.val who)))
    (fuel : Nat) (left right : setup.commitRecoveryProtocol.History)
    (leftKept : TracePrefix prior left.trace) (rightKept : TracePrefix prior right.trace)
    (word : setup.omissionRecall left.trace = setup.omissionRecall right.trace)
    (within : left.trace.length + fuel + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    (setup.commitRecoveryModel.runBehavioralFrom leftProfile fuel left).map
        (fun history => setup.omissionRecall history.trace) =
      (setup.commitRecoveryModel.runBehavioralFrom rightProfile fuel right).map
        (fun history => setup.omissionRecall history.trace) := by
  classical
  induction fuel generalizing left right with
  | zero => simpa only [InformationModel.runBehavioralFrom,
      runRandomizedFor, PMF.pure_map] using congrArg PMF.pure word
  | succ fuel ih =>
      have inside : left.trace.length + ProtocolState.commitEnd setup.program first.point <
          prior.length + ProtocolState.remaining setup.program first.point := by omega
      obtain ⟨point, pointState, atCommit, _ending, _rank⟩ :=
        setup.commitRecovery_prefix_inside_commit first prior committing left.trace leftKept inside
      have leftRunning : ¬ setup.commitRecoveryProtocol.terminal left.state := by
        rw [pointState]
        intro ended
        have zero := (ProtocolState.remaining_zero_iff_terminal setup.program point.point).mpr ended
        have positive := ProtocolState.commitEnd_lt_remaining setup.program point.point atCommit
        omega
      have clock : left.trace.length = right.trace.length := by
        have lengths := congrArg List.length word
        simpa only [omissionRecall, List.length_map, setup.recoveryJointRecall_length] using lengths
      obtain ⟨other, otherState, otherCommit, _otherEnding, _otherRank⟩ :=
        setup.commitRecovery_prefix_inside_commit first prior committing right.trace rightKept
          (by omega)
      have rightRunning : ¬ setup.commitRecoveryProtocol.terminal right.state := by
        rw [otherState]
        intro ended
        have zero := (ProtocolState.remaining_zero_iff_terminal setup.program other.point).mpr ended
        have positive := ProtocolState.commitEnd_lt_remaining setup.program other.point otherCommit
        omega
      have one : (setup.commitRecoveryModel.runBehavioralFrom leftProfile 1 left).map
          (fun history => setup.omissionRecall history.trace) =
        (setup.commitRecoveryModel.runBehavioralFrom rightProfile 1 right).map
          (fun history => setup.omissionRecall history.trace) := by
        rw [setup.one_step_omission_word leftProfile left leftRunning,
          setup.one_step_omission_word rightProfile right rightRunning,
          matched left right leftKept rightKept word inside leftRunning rightRunning, word]
      rw [show fuel + 1 = 1 + fuel by omega,
        setup.commitRecoveryModel.runBehavioralFrom_add,
        setup.commitRecoveryModel.runBehavioralFrom_add, PMF.map_bind, PMF.map_bind]
      apply bind_eq_of_map_eq _ _ (fun history => setup.omissionRecall history.trace)
        (fun history => setup.omissionRecall history.trace) one
      intro nextLeft leftSupported nextRight rightSupported nextWord
      have keptLeft := ReachesWithin.tracePrefix
        (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin
          leftProfile 1 left nextLeft leftSupported)
      have keptRight := ReachesWithin.tracePrefix
        (setup.commitRecoveryModel.runBehavioralFrom_reachesWithin
          rightProfile 1 right nextRight rightSupported)
      have consumed := setup.commitRecoveryModel.length_of_mem_support_runBehavioralFrom_one
        leftProfile leftRunning leftSupported
      exact ih nextLeft nextRight (leftKept.trans keptLeft) (rightKept.trans keptRight)
        nextWord (by omega)

omit [Fintype Player] in
theorem prefix_excluded
    {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (trace : setup.commitRecoveryProtocol.Trace after)
    (kept : TracePrefix prior trace) :
    (setup.commitRecoveryPublic before).1 ⊆ (setup.commitRecoveryPublic after).1 := by
  induction kept with
  | refl => exact Finset.Subset.refl _
  | extend _ joint legal reached ih =>
      exact ih.trans (setup.commitRecovery_step_excluded_subset joint legal reached)

end Vegas.SourceProgram.Setup
