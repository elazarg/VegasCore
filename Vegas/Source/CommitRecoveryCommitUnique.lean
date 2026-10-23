/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryInstructions
import Vegas.Source.CommitRecoveryFrontier
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Original commitment instructions determine their actual source history -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- A raw commitment instruction has no nature branch, including omitted,
excluded-owner and accepted failed bindings. -/
theorem recoveryStep_commit_pure : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
    atCommit program point = true →
      ∃ result, recoveryStep program point excluded joint = PMF.pure result
  | _, _, .ret _, _, _, _, committing => by cases committing
  | _, _, .sample _ _ _ next, point, excluded, joint, committing => by
      cases point with
      | inl _ => cases committing
      | inr point =>
          obtain ⟨result, pure⟩ := recoveryStep_commit_pure next point excluded joint committing
          simp only [recoveryStep, Sum.elim_inr, pure, PMF.pure_map]
          exact ⟨_, rfl⟩
  | _, _, .commit _ _ _ _ next, point, excluded, joint, committing => by
      cases point with
      | inl _ =>
          simp only [recoveryStep, Sum.elim_inl]
          split <;> exact ⟨_, rfl⟩
      | inr point =>
          obtain ⟨result, pure⟩ := recoveryStep_commit_pure next point excluded joint committing
          simp only [recoveryStep, Sum.elim_inr, pure, PMF.pure_map]
          exact ⟨_, rfl⟩
  | _, _, .reveal _ _ _ _ _ _ next, point, excluded, joint, committing => by
      cases point with
      | inl _ => cases committing
      | inr point =>
          obtain ⟨result, pure⟩ := recoveryStep_commit_pure next point excluded joint committing
          simp only [recoveryStep, Sum.elim_inr, pure, PMF.pure_map]
          exact ⟨_, rfl⟩

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- The real automatic close preserves determinism of one commitment
instruction, including a last instruction which retries or exhausts a block. -/
theorem step_unique_of_commit (state : CommitRecoveryState program)
    (committing : ProtocolState.atCommit program state.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (first second : CommitRecoveryState program)
    (firstSupport : first ∈ (state.step joint).support)
    (secondSupport : second ∈ (state.step joint).support) : first = second := by
  obtain ⟨left, leftSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstSupport
  obtain ⟨right, rightSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondSupport
  let raw := ProtocolState.recoveryStep program state.point state.excluded joint
  let keep := fun result (supported : result ∈ raw.support) =>
    ProtocolState.recoveryStep_excluded_monotone program state.point state.excluded joint
      result supported
  have leftRaw : left.1 ∈ raw.support := by
    rw [← map_val_pmfToSubtype raw keep]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨left, leftSupport, rfl⟩
  have rightRaw : right.1 ∈ raw.support := by
    rw [← map_val_pmfToSubtype raw keep]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨right, rightSupport, rfl⟩
  obtain ⟨result, pure⟩ := ProtocolState.recoveryStep_commit_pure program state.point
    state.excluded joint committing
  change left.1 ∈ (ProtocolState.recoveryStep program state.point state.excluded joint).support
    at leftRaw
  change right.1 ∈ (ProtocolState.recoveryStep program state.point state.excluded joint).support
    at rightRaw
  rw [pure, PMF.mem_support_pure_iff] at leftRaw rightRaw
  have equal : left = right := Subtype.ext (leftRaw.trans rightRaw.symm)
  cases equal
  rfl

/-- Before the final instruction of the saved commitment window, a real step
cannot close or sample nature. Its exact remaining rank and endpoint persist. -/
theorem step_inside_commit (state : CommitRecoveryState program) (frontier : state.BlockFrontier)
    (committing : ProtocolState.atCommit program state.point = true)
    (inside : ProtocolState.commitEnd program state.point + 1 <
      ProtocolState.remaining program state.point)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support) :
    ProtocolState.atCommit program next.point = true ∧
      ProtocolState.commitEnd program next.point = ProtocolState.commitEnd program state.point ∧
      ProtocolState.remaining program next.point + 1 =
        ProtocolState.remaining program state.point := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have running : ¬ ProtocolState.terminal program state.point := by
    intro terminal
    have zero := (ProtocolState.remaining_zero_iff_terminal program state.point).mpr terminal
    omega
  have rank := ProtocolState.recoveryStep_remaining program state.point state.excluded joint
    result.1 running raw
  obtain ⟨nextCommit, sameEnd⟩ :=
    (ProtocolState.recoveryStep_commit_cursor program state.point state.excluded joint result.1
      committing raw).resolve_right (by rintro ⟨_notCommit, ended⟩; omega)
  have savedCommit : ProtocolState.atCommit program state.saved = true := by
    rcases frontier with ⟨saved, _live, _end⟩ | same
    · exact saved
    · rwa [same]
  have savedEnd : ProtocolState.commitEnd program state.point =
      ProtocolState.commitEnd program state.saved := by
    rcases frontier with ⟨_saved, _live, endPoint⟩ | same
    · exact endPoint
    · rw [same]
  let image := state.install result.1 result.2
  have unfinished : ¬ image.Finished := by
    rintro ⟨_saved, ended⟩
    change ProtocolState.remaining program result.1.1 =
      ProtocolState.commitEnd program state.saved at ended
    omega
  have unchanged : image.close = image := by
    unfold close
    have imageCommit : ProtocolState.atCommit program image.saved = true := savedCommit
    rw [ite_eq_right unfinished, ite_eq_left imageCommit]
  change ProtocolState.atCommit program image.close.point = true ∧ _
  rw [unchanged]
  exact ⟨nextCommit, sameEnd, rank⟩

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The original instruction recall counts every real setup or source step. -/
theorem recoveryJointRecall_length {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.recoveryJointRecall trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend _ _ _ _ ih => exact congrArg Nat.succ ih

/-- Every actual prefix strictly inside the current commitment window is
still at a commitment instruction with its original endpoint and exact rank. -/
theorem commitRecovery_prefix_inside_commit
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (retained : TracePrefix prior trace)
    (inside : trace.length + ProtocolState.commitEnd setup.program first.point <
      prior.length + ProtocolState.remaining setup.program first.point) :
    ∃ current : CommitRecoveryState setup.program, state = some current ∧
      ProtocolState.atCommit setup.program current.point = true ∧
      ProtocolState.commitEnd setup.program current.point =
        ProtocolState.commitEnd setup.program first.point ∧
      trace.length + ProtocolState.remaining setup.program current.point =
        prior.length + ProtocolState.remaining setup.program first.point := by
  induction retained with
  | refl => exact ⟨first, rfl, committing, rfl, rfl⟩
  | @extend source target earlier kept joint legal reached ih =>
      have previousInside : earlier.length + ProtocolState.commitEnd setup.program first.point <
          prior.length + ProtocolState.remaining setup.program first.point := by
        simp only [Trace.length] at inside
        omega
      obtain ⟨middle, rfl, middleCommit, middleEnd, middleRank⟩ := ih previousInside
      obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      have middleInside : ProtocolState.commitEnd setup.program middle.point + 1 <
          ProtocolState.remaining setup.program middle.point := by
        simp only [Trace.length] at inside
        omega
      obtain ⟨nextCommit, nextEnd, nextRank⟩ := middle.step_inside_commit
        (setup.commitRecovery_blockFrontier earlier) middleCommit middleInside joint next supported
      exact ⟨next, rfl, nextCommit, nextEnd.trans middleEnd, by
        simp only [Trace.length]
        omega⟩


/-- Within one actual commitment window, the same original instruction recall
from the same prior trace determines the entire source history. The last step
may perform the real automatic retry or exhaustion close. -/
private theorem history_eq_of_commit_prefix
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {leftState rightState : setup.commitRecoveryProtocol.State}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior leftTrace) (rightRetained : TracePrefix prior rightTrace)
    (sameWord : setup.recoveryJointRecall leftTrace = setup.recoveryJointRecall rightTrace)
    (within : leftTrace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    (⟨leftState, leftTrace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨rightState, rightTrace⟩ := by
  induction leftRetained generalizing rightState with
  | refl =>
      have length := congrArg List.length sameWord
      rw [setup.recoveryJointRecall_length, setup.recoveryJointRecall_length] at length
      exact rightRetained.eq_of_length length
  | @extend source target earlier kept joint legal reached ih =>
      cases rightRetained with
      | refl =>
          have length := congrArg List.length sameWord
          rw [setup.recoveryJointRecall_length, setup.recoveryJointRecall_length] at length
          have lower := kept.length_le
          simp only [Trace.length] at length
          omega
      | @extend rightSource rightTarget rightEarlier rightKept rightJoint rightLegal rightReached =>
          have words := List.cons.inj sameWord
          have earlierWithin : earlier.length + ProtocolState.commitEnd setup.program first.point ≤
              prior.length + ProtocolState.remaining setup.program first.point := by
            simp only [Trace.length] at within
            omega
          have previous := ih rightEarlier rightKept words.2 earlierWithin
          cases previous
          have earlierInside : earlier.length + ProtocolState.commitEnd setup.program first.point <
              prior.length + ProtocolState.remaining setup.program first.point := by
            simp only [Trace.length] at within
            omega
          obtain ⟨current, rfl, currentCommit, _sameEnd, _rank⟩ :=
            setup.commitRecovery_prefix_inside_commit first prior committing earlier kept
              earlierInside
          cases words.1
          obtain ⟨leftNext, leftSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          obtain ⟨rightNext, rightSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rightReached
          cases current.step_unique_of_commit currentCommit joint leftNext rightNext
            leftSupport rightSupport
          rfl

/-- The same actual prior and exact original joint word determine a whole
commitment continuation, even when its final endpoint was not predetermined.
No nature draw or determinism premise is supplied. -/
theorem commitRecovery_history_eq_of_commit_window
    (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (committing : ProtocolState.atCommit setup.program first.point = true)
    {leftState rightState : setup.commitRecoveryProtocol.State} {leftFuel rightFuel : Nat}
    (leftTrace : setup.commitRecoveryProtocol.Trace leftState)
    (rightTrace : setup.commitRecoveryProtocol.Trace rightState)
    (leftReached : setup.commitRecoveryProtocol.ReachesWithin leftFuel
      ⟨some first, prior⟩ ⟨leftState, leftTrace⟩)
    (rightReached : setup.commitRecoveryProtocol.ReachesWithin rightFuel
      ⟨some first, prior⟩ ⟨rightState, rightTrace⟩)
    (sameWord : setup.recoveryJointRecall leftTrace = setup.recoveryJointRecall rightTrace)
    (within : leftTrace.length + ProtocolState.commitEnd setup.program first.point ≤
      prior.length + ProtocolState.remaining setup.program first.point) :
    (⟨leftState, leftTrace⟩ : setup.commitRecoveryProtocol.History) =
      ⟨rightState, rightTrace⟩ := by
  have leftRetained : TracePrefix prior leftTrace := leftReached.tracePrefix
  have rightRetained : TracePrefix prior rightTrace := rightReached.tracePrefix
  exact history_eq_of_commit_prefix setup first prior committing leftTrace rightTrace
    leftRetained rightRetained sameWord within

end Setup
end Vegas.SourceProgram
