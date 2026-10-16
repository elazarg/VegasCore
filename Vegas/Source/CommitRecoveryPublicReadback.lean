/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPublicHistory
import Vegas.Source.CommitRecoveryNonCommitObservation
import Vegas.Source.CommitRecoveryAttemptReset
import Vegas.Source.CommitRecoveryRanks
import Vegas.Source.CommitRecoveryOwnHistory

/-! # Actual earlier public source observations through arbitrary retries -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Padding is the identity outside a private commitment interval. -/
theorem automaticCommitBlock_of_not_atCommit :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program), atCommit program point = false →
      automaticCommitBlock program point = point
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, absent => by
      cases point with
      | inl => rfl
      | inr point => exact congrArg Sum.inr (automaticCommitBlock_of_not_atCommit next point absent)
  | _, _, .commit _ _ _ _ next, point, absent => by
      cases point with
      | inl => cases absent
      | inr point => exact congrArg Sum.inr (automaticCommitBlock_of_not_atCommit next point absent)
  | _, _, .reveal _ _ _ _ _ _ next, point, absent => by
      cases point with
      | inl => rfl
      | inr point => exact congrArg Sum.inr (automaticCommitBlock_of_not_atCommit next point absent)

/-- Padding reaches at least the actual current instruction rank. -/
theorem position_le_automaticCommitBlock {Γ : SourceCtx Player L} {O : Finset VarId}
    (who : Player) (program : SourceProgram Player L Γ O) (point : ProtocolState program) :
    ProtocolView.position who program (observe who program point) ≤
      ProtocolView.position who program
        (observe who program (automaticCommitBlock program point)) :=
  by
  have before := ProtocolView.position_add_remaining who program point
  have after := ProtocolView.position_add_remaining who program
    (automaticCommitBlock program point)
  rw [automaticCommitBlock_remaining] at after
  have bounded := commitEnd_le_remaining program point
  omega

end ProtocolState

namespace Setup

/-- One actual initialized source step preserves every public rank already
in its padded commitment image. Retries may lower the live rank, while this
public readback remains available at its original static address. -/
theorem commitRecovery_public_rank_step
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (before after : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some before))
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some before) joint)
    (supported : some after ∈
      (setup.commitRecoveryProtocol.step (some before) ⟨joint, legal⟩).support)
    (survives : who ∉ before.excluded) (rank : Nat)
    (bounded : rank ≤ ProtocolView.position who setup.program
      (ProtocolState.observe who setup.program
        (ProtocolState.automaticCommitBlock setup.program before.point))) :
    rank ≤ ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program after.point)) ∧
      (ProtocolView.atRank who setup.program rank
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program after.point))).map
            (ProtocolView.publicOnly who setup.program) =
      (ProtocolView.atRank who setup.program rank
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program before.point))).map
            (ProtocolView.publicOnly who setup.program) := by
  by_cases committing : ProtocolState.atCommit setup.program before.point = true
  · have same := setup.commitRecovery_commit_public_readback who before after trace committing
      joint legal supported
    refine ⟨?_, ?_⟩
    · have positions := congrArg (ProtocolView.position who setup.program) same
      simp only [ProtocolView.position_publicOnly] at positions
      exact positions.symm ▸ bounded
    · simpa only [ProtocolView.atRank_publicOnly] using
        congrArg (ProtocolView.atRank who setup.program rank) same
  · have absent : ProtocolState.atCommit setup.program before.point = false :=
      Bool.eq_false_iff.mpr committing
    obtain ⟨target, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have targetEq : target = after := Option.some.inj equal
    subst target
    obtain ⟨raw, member, installed⟩ := before.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier trace) absent joint after reached
    rw [installed]
    have rankBefore : rank ≤ ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program before.point) := by
      simpa only [ProtocolState.automaticCommitBlock_of_not_atCommit _ _ absent] using bounded
    have progress := ProtocolState.recoveryStep_remaining setup.program before.point
      before.excluded joint raw legal.1 member
    have beforePosition := ProtocolView.position_add_remaining who setup.program before.point
    have rawPosition := ProtocolView.position_add_remaining who setup.program raw.1
    refine ⟨?_, ?_⟩
    · have padded := ProtocolState.position_le_automaticCommitBlock who setup.program raw.1
      change rank ≤ ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program raw.1))
      omega
    · change (ProtocolView.atRank who setup.program rank
          (ProtocolState.observe who setup.program
            (ProtocolState.automaticCommitBlock setup.program raw.1))).map _ = _
      rw [ProtocolState.atRank_automaticCommitBlock_public who setup.program raw.1 rank
        (by omega)]
      rw [ProtocolState.automaticCommitBlock_of_not_atCommit _ _ absent]
      exact congrArg (Option.map (ProtocolView.publicOnly who setup.program))
        (ProtocolView.atRank_recoveryStep who setup.program before.point before.excluded joint
          raw member survives rank rankBefore)

/-- The original source exclusion event remains permanent along genuine
history prefixes; this includes setup and exhausted closes. -/
theorem commitRecovery_public_excluded_of_reaches
    (setup : Setup (Player := Player) (L := L)) {fuel : Nat}
    {start last : setup.commitRecoveryProtocol.History}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel start last) :
    (setup.commitRecoveryPublic start.state).1 ⊆ (setup.commitRecoveryPublic last.state).1 := by
  induction reached with
  | refl => exact Finset.Subset.refl _
  | step joint legal supported _ ih =>
      exact (setup.commitRecovery_step_excluded_subset joint legal supported).trans ih

/-- Every genuine earlier public observation, including observations in a
voided attempt, is read from the final padded public typed store at its
original rank. No earlier private word is reconstructed. -/
theorem commitRecovery_public_rank_of_reaches
    (setup : Setup (Player := Player) (L := L)) (who : Player) {fuel : Nat}
    {first last : setup.commitRecoveryProtocol.History}
    (reached : setup.commitRecoveryProtocol.ReachesWithin fuel first last)
    (before after : CommitRecoveryState setup.program)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (survives : who ∉ after.excluded) :
    (ProtocolView.atRank who setup.program
      (ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program before.point))
      (ProtocolState.observe who setup.program
        (ProtocolState.automaticCommitBlock setup.program after.point))).map
          (ProtocolView.publicOnly who setup.program) =
      some (ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program before.point)) := by
  have propagate : ∀ {budget : Nat} {start finish : setup.commitRecoveryProtocol.History},
      setup.commitRecoveryProtocol.ReachesWithin budget start finish →
      ∀ initial final, start.state = some initial → finish.state = some final →
      who ∉ final.excluded → ∀ rank,
      rank ≤ ProtocolView.position who setup.program
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program initial.point)) →
      (ProtocolView.atRank who setup.program rank
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program final.point))).map
            (ProtocolView.publicOnly who setup.program) =
      (ProtocolView.atRank who setup.program rank
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program initial.point))).map
            (ProtocolView.publicOnly who setup.program) := by
    intro budget start finish path
    induction path with
    | refl =>
        intro initial final firstState lastState _ rank _
        have equal := Option.some.inj (firstState.symm.trans lastState)
        subst final
        rfl
    | @step budget start target joint legal next supported rest ih =>
        intro initial final firstState lastState active rank bounded
        rcases start with ⟨startState, startTrace⟩
        change startState = some initial at firstState
        subst startState
        have actual := supported
        obtain ⟨nextState, nextReached, nextEq⟩ := (PMF.mem_support_map_iff _ _ _).mp actual
        have nextActive : who ∉ nextState.excluded := by
          intro excluded
          have monotone := setup.commitRecovery_public_excluded_of_reaches rest
          change (setup.commitRecoveryPublic next).1 ⊆
            (setup.commitRecoveryPublic target.state).1 at monotone
          rw [← nextEq, lastState] at monotone
          exact active (monotone excluded)
        have initialActive : who ∉ initial.excluded := by
          intro excluded
          exact nextActive (initial.step_excluded_monotone joint nextState nextReached excluded)
        have beforeTrace : setup.commitRecoveryProtocol.Trace (some initial) :=
          startTrace
        have physical : some nextState ∈
            (setup.commitRecoveryProtocol.step (some initial)
              ⟨joint, legal⟩).support :=
          nextEq ▸ actual
        obtain ⟨nextBound, stepEq⟩ := setup.commitRecovery_public_rank_step who initial nextState
          beforeTrace joint legal physical initialActive rank bounded
        exact (ih nextState final nextEq.symm lastState active rank nextBound).trans stepEq
  have read := propagate reached before after firstState lastState survives _
    (ProtocolState.position_le_automaticCommitBlock who setup.program before.point)
  rw [ProtocolState.atRank_automaticCommitBlock_public who setup.program before.point _ le_rfl,
    ProtocolView.atRank_position] at read
  exact read

end Setup

end Vegas.SourceProgram
