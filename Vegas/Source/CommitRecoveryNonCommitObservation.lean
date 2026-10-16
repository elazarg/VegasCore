/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryObservation
import Vegas.Source.CommitRecoveryFrontier
import Vegas.Source.CommitRecoveryNonCommitPath
import Vegas.Source.CommitRecoveryObservedMemory
import Vegas.Source.CommitRecoveryPublicControl
import Vegas.Source.CommitRecoveryPublicRanks

/-! # Observable public successors of noncommitment recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]


namespace CommitRecoveryState

/-- An actual noncommitment step installs its result directly, without retry. -/
theorem step_noncommit_atPoint {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (frontier : state.BlockFrontier)
    (notCommit : ProtocolState.atCommit program state.point = false)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (reached : next ∈ (state.step joint).support) :
    ∃ result ∈ (ProtocolState.recoveryStep program state.point state.excluded joint).support,
      next = atPoint result.1 result.2 state.generation := by
  obtain ⟨result, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  let law := ProtocolState.recoveryStep program state.point state.excluded joint
  let keep := fun value (member : value ∈ law.support) =>
    ProtocolState.recoveryStep_excluded_monotone program state.point state.excluded joint
      value member
  have raw : result.1 ∈ law.support := by
    rw [← map_val_pmfToSubtype law keep]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, supported, rfl⟩
  have saved : ProtocolState.atCommit program state.saved = false := by
    rw [frontier.saved_eq_point_of_not_atCommit notCommit, notCommit]
  refine ⟨result.1, raw, ?_⟩
  simp only [close, Finished, install, saved, Bool.false_eq_true, false_and, ↓reduceIte]

/-- An actual public instruction installs its observed exclusion update and
new saved point exactly; no prior private signal or intended action is needed. -/
theorem step_noncommit_public_controls {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (frontier : state.BlockFrontier)
    (notCommit : ProtocolState.atCommit program state.point = false)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (reached : next ∈ (state.step joint).support) (who : Player) :
    next.excluded = ProtocolView.publicSuccessorExclusions who program
        (ProtocolView.publicOnly who program (ProtocolState.observe who program state.point))
        (ProtocolView.publicOnly who program (ProtocolState.observe who program next.point))
        state.excluded ∧
      next.generation = state.generation ∧ next.saved = next.point := by
  obtain ⟨result, supported, rfl⟩ :=
    state.step_noncommit_atPoint frontier notCommit joint next reached
  exact ⟨ProtocolState.recoveryStep_noncommit_public_excluded who program state.point
    notCommit state.excluded joint result supported, rfl, rfl⟩

end CommitRecoveryState

namespace Setup

/-- At genuine noncommitment instructions, equal before and next public
views determine the full next public signal.
Permanent exclusions are arbitrary and remain in the actual source histories. -/
theorem commitRecovery_noncommit_public_eq (setup : Setup (Player := Player) (L := L))
    (who : Player) (first second : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some second))
    (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
    (firstLegal : setup.commitRecoveryProtocol.Legal (some first) firstJoint)
    (secondLegal : setup.commitRecoveryProtocol.Legal (some second) secondJoint)
    (firstAfter secondAfter : setup.commitRecoveryProtocol.State)
    (firstReached : firstAfter ∈
      (setup.commitRecoveryProtocol.step (some first) ⟨firstJoint, firstLegal⟩).support)
    (secondReached : secondAfter ∈
      (setup.commitRecoveryProtocol.step (some second) ⟨secondJoint, secondLegal⟩).support)
    (notCommit : ProtocolState.atCommit setup.program first.point = false)
    (before : (setup.commitRecoveryPrivate who (some first)).map
        (ProtocolView.publicOnly who setup.program) =
      (setup.commitRecoveryPrivate who (some second)).map
        (ProtocolView.publicOnly who setup.program))
    (publicBefore : setup.commitRecoveryPublic (some first) =
      setup.commitRecoveryPublic (some second))
    (after : (setup.commitRecoveryPrivate who firstAfter).map
        (ProtocolView.publicOnly who setup.program) =
      (setup.commitRecoveryPrivate who secondAfter).map
        (ProtocolView.publicOnly who setup.program)) :
    setup.commitRecoveryPublic firstAfter = setup.commitRecoveryPublic secondAfter := by
  have observedBefore : ProtocolView.publicOnly who setup.program
      (ProtocolState.observe who setup.program first.point) =
    ProtocolView.publicOnly who setup.program
      (ProtocolState.observe who setup.program second.point) := Option.some.inj before
  have exclusions : first.excluded = second.excluded := congrArg Prod.fst publicBefore
  have generation : first.generation = second.generation :=
    congrArg (fun info => info.2.1) publicBefore
  have secondNotCommit : ProtocolState.atCommit setup.program second.point = false := by
    have kind := (ProtocolState.public_control who setup.program first.point second.point
      observedBefore).2.1
    exact kind ▸ notCommit
  obtain ⟨left, leftReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstReached
  obtain ⟨right, rightReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondReached
  obtain ⟨leftExcluded, leftGeneration, leftSaved⟩ := first.step_noncommit_public_controls
    (setup.commitRecovery_blockFrontier firstTrace) notCommit firstJoint left leftReached who
  obtain ⟨rightExcluded, rightGeneration, rightSaved⟩ := second.step_noncommit_public_controls
    (setup.commitRecovery_blockFrontier secondTrace) secondNotCommit secondJoint right
      rightReached who
  have observedAfter : ProtocolView.publicOnly who setup.program
      (ProtocolState.observe who setup.program left.point) =
    ProtocolView.publicOnly who setup.program
      (ProtocolState.observe who setup.program right.point) :=
    Option.some.inj after
  have nextExclusions : left.excluded = right.excluded := by
    rw [leftExcluded, rightExcluded, observedBefore, observedAfter, exclusions]
  have leftRank := ProtocolView.position_add_remaining who setup.program left.point
  have rightRank := ProtocolView.position_add_remaining who setup.program right.point
  have positions := congrArg (ProtocolView.position who setup.program) observedAfter
  simp only [ProtocolView.position_publicOnly] at positions
  have rank : ProtocolState.remaining setup.program left.point =
      ProtocolState.remaining setup.program right.point := by omega
  simp only [commitRecoveryPublic, leftSaved, rightSaved, nextExclusions,
    leftGeneration, rightGeneration, generation, rank]

end Setup
end Vegas.SourceProgram
