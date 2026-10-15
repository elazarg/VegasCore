/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitBlockRecovery
import Vegas.Source.CommitRecoveryFrontier
import Vegas.Source.CommitPrefixSplitting
import GameTheory.Protocol.ActionRestriction

/-! # Nonomitting source play stays clear through its commitment window -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

theorem commit_noMiss_cursor {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (committing : ProtocolState.atCommit program state.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (noMiss : ∀ who, CommitRecoveryMove.missed (joint who) = false)
    (next : CommitRecoveryState program) (reached : next ∈ (state.step joint).support) :
    next.excluded = ∅ ∧
      ProtocolState.remaining program next.point + 1 = ProtocolState.remaining program state.point ∧
      ((ProtocolState.atCommit program next.point = true ∧
          ProtocolState.commitEnd program next.point =
            ProtocolState.commitEnd program state.point) ∨
        ProtocolState.remaining program next.point =
          ProtocolState.commitEnd program state.point) := by
  obtain ⟨afterClear, typed⟩ := state.commit_noMiss_support clear committing joint noMiss next
    reached
  have running : ¬ ProtocolState.terminal program state.point := by
    intro stopped
    have zero := (ProtocolState.remaining_zero_iff_terminal program state.point).mpr stopped
    have below := ProtocolState.commitEnd_lt_remaining program state.point committing
    omega
  have consumed := ProtocolState.remaining_step program state.point next.point
    (fun who => (joint who).map (·.action)) running typed
  have raw : (next.point, ∅) ∈
      (ProtocolState.recoveryStep program state.point ∅ joint).support := by
    rw [ProtocolState.recoveryStep_commit_joint program state.point joint committing noMiss]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨next.point, typed, rfl⟩
  have cursor := ProtocolState.recoveryStep_commit_cursor program state.point ∅ joint
    (next.point, ∅) committing raw
  exact ⟨afterClear, consumed, cursor.imp id And.right⟩

end CommitRecoveryState

namespace Setup

variable [Fintype Player] (setup : Setup (Player := Player) (L := L))

/-- A profile with no missing choices remains clear for every instruction in
the actual remaining commitment window, including the real automatic close.
Accepted failed bindings are allowed throughout. -/
theorem commitRecovery_run_nonmissing_commit_clear
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (nonmissing : ∀ (history : setup.commitRecoveryProtocol.History),
      ¬ setup.commitRecoveryProtocol.terminal history.state → ∀ who choice,
        choice ∈ (profile who (setup.commitRecoveryModel.infoOf who history.trace)).support →
          CommitRecoveryMove.missed choice.1 = false)
    (fuel : Nat) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current)) (clear : current.excluded = ∅)
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (within : fuel + ProtocolState.commitEnd setup.program current.point ≤
      ProtocolState.remaining setup.program current.point)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralFrom profile fuel
      ⟨some current, trace⟩).support) : setup.CommitRecoveryClear final.state := by
  classical
  induction fuel generalizing current final with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact clear
  | succ fuel ih =>
      let start : setup.commitRecoveryProtocol.History := ⟨some current, trace⟩
      have running : ¬ setup.commitRecoveryProtocol.terminal start.state := by
        intro stopped
        have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr
          stopped
        have below := ProtocolState.commitEnd_lt_remaining setup.program current.point committing
        omega
      rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile fuel running,
        PMF.support_bind] at supported
      obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
      rw [PMF.mem_support_bindOnSupport_iff] at continued
      obtain ⟨target, reached, child⟩ := continued
      have marginal : draw.1 ∈ ((setup.commitRecoveryModel.behavioralJoint profile trace
          running).map Subtype.val).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
      rw [setup.commitRecoveryModel.behavioralJoint_map_val,
        independentProduct_support_iff] at marginal
      have noMiss (who : Player) : CommitRecoveryMove.missed (draw.1 who) = false := by
        obtain ⟨choice, chosen, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp (marginal who)
        rw [← equal]
        exact nonmissing start running who choice chosen
      obtain ⟨next, nextReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      have nextCursor := current.commit_noMiss_cursor clear committing draw.1 noMiss next
        nextReached
      by_cases last : fuel = 0
      · subst fuel
        cases (PMF.mem_support_pure_iff _ _).mp child
        exact nextCursor.1
      · have cursor : ProtocolState.atCommit setup.program next.point = true ∧
            ProtocolState.commitEnd setup.program next.point =
              ProtocolState.commitEnd setup.program current.point := by
          rcases nextCursor.2.2 with cursor | atEnd
          · exact cursor
          · omega
        apply ih next _ nextCursor.1 cursor.1 _ final child
        rw [cursor.2]
        omega

end Setup

namespace CommitPrefix

/-- Every typed initial commitment segment fits inside the actual maximal
commitment window, even if its remaining suffix starts with more bindings. -/
theorem length_le_commit_window {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (entry : Config Player L Γ) :
    block.length + ProtocolState.commitEnd (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) entry) ≤
      ProtocolState.remaining (block.prepend suffix)
        (ProtocolState.entry (block.prepend suffix) entry) := by
  have endpoint : ProtocolState.commitEnd (block.prepend suffix)
      (ProtocolState.entry (block.prepend suffix) entry) ≤ instructionCount suffix := by
    simp only [ProtocolState.commitEnd_entry]
    induction block with
    | nil =>
        simpa only [prepend, ProtocolState.commitEnd_entry, ProtocolState.remaining_entry] using
          ProtocolState.commitEnd_le_remaining suffix (ProtocolState.entry suffix entry)
    | commit name owner fresh guard rest ih =>
        exact ih suffix (automaticCommit name owner _ entry)
  rw [ProtocolState.remaining_entry, instructionCount_prepend]
  omega

end CommitPrefix
end Vegas.SourceProgram
