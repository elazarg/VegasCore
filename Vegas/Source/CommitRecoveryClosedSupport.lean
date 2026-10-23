/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryClosedSplice
import Vegas.Source.CommitRecoverySpliceSupport

/-! # Supported original recovery histories under owner substitution

Raw original instructions are combined before the existing attempt closure.
All permanent histories, actual reset branches and original chance draws
remain in the genuine source protocol.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- The existing installation of a raw result retains the combined saved checkpoint. -/
theorem splice_install (focal : Player) (mine others : CommitRecoveryState program)
    (left right : ProtocolState program × Finset Player)
    (leftMonotone : mine.excluded ⊆ left.2) (rightMonotone : others.excluded ⊆ right.2) :
    splice focal (mine.install left leftMonotone) (others.install right rightMonotone) =
      (splice focal mine others).install
        (ProtocolState.splice focal program left.1 right.1, right.2) rightMonotone := rfl

/-- Combining two actual supported raw instructions produces a supported
original automatically closed instruction. The actual close is derived,
including retry and exhausted restore; it is not supplied as a target law. -/
theorem step_splice_support_of_raw (focal : Player) (mine others : CommitRecoveryState program)
    (metadata : mine.MetadataEq others)
    (before : ProtocolView.publicOnly focal program
        (ProtocolState.observe focal program mine.point) =
      ProtocolView.publicOnly focal program (ProtocolState.observe focal program others.point))
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (left : {result : ProtocolState program × Finset Player // mine.excluded ⊆ result.2})
    (right : {result : ProtocolState program × Finset Player // others.excluded ⊆ result.2})
    (leftRaw : left.1 ∈
      (ProtocolState.recoveryStep program mine.point mine.excluded leftJoint).support)
    (rightRaw : right.1 ∈
      (ProtocolState.recoveryStep program others.point others.excluded rightJoint).support)
    (sameExcluded : left.1.2 = right.1.2)
    (after : ProtocolView.publicOnly focal program (ProtocolState.observe focal program left.1.1) =
      ProtocolView.publicOnly focal program (ProtocolState.observe focal program right.1.1)) :
    splice focal (mine.install left.1 left.2).close (others.install right.1 right.2).close ∈
      ((splice focal mine others).step
        (Function.update rightJoint focal (leftJoint focal))).support := by
  have rightMember : right.1 ∈
      (ProtocolState.recoveryStep program others.point mine.excluded rightJoint).support := by
    simpa only [metadata.2.2.1] using rightRaw
  have rawMember := ProtocolState.recoveryStep_splice_support focal program mine.point others.point
    metadata.1 before mine.excluded leftJoint rightJoint left.1 leftRaw right.1 rightMember
      sameExcluded after
  let mixed := splice focal mine others
  let joint := Function.update rightJoint focal (leftJoint focal)
  let raw := ProtocolState.recoveryStep program mixed.point mixed.excluded joint
  let keep := fun result (member : result ∈ raw.support) =>
    ProtocolState.recoveryStep_excluded_monotone program mixed.point mixed.excluded
      joint result member
  have supported : (ProtocolState.splice focal program left.1.1 right.1.1, right.1.2) ∈
      ((pmfToSubtype raw keep).map Subtype.val).support := by
    rw [map_val_pmfToSubtype]
    simpa only [raw, mixed, joint, splice, metadata.2.2.1] using rawMember
  obtain ⟨result, resultMember, resultEq⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨result, resultMember, ?_⟩
  have installation : (mine.install left.1 left.2).MetadataEq
      (others.install right.1 right.2) :=
    ⟨ProtocolState.recoveryStep_metadata program mine.point others.point metadata.1
        mine.excluded leftJoint rightJoint left.1 leftRaw right.1 rightMember,
      metadata.2.1, sameExcluded, metadata.2.2.2.1, metadata.2.2.2.2⟩
  rw [splice_close focal _ _ installation, splice_install]
  cases result with
  | mk actual monotone =>
      change actual = _ at resultEq
      subst actual
      rfl

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

private theorem installed_close_of_not_committing
    (state : CommitRecoveryState setup.program)
    (notCommit : ProtocolState.atCommit setup.program state.saved = false)
    (result : SourceProgram.ProtocolState setup.program × Finset Player)
    (monotone : state.excluded ⊆ result.2) :
    (state.install result monotone).close =
      CommitRecoveryState.atPoint result.1 result.2 state.generation := by
  simp only [CommitRecoveryState.close, CommitRecoveryState.Finished,
    CommitRecoveryState.install, notCommit, Bool.false_eq_true, false_and, ↓reduceIte]

/-- Actual original source histories supply the raw support needed for owner
substitution. Publicly matching source successors suffice even when the real
close restores a failed commitment attempt and hides its old raw cursor. -/
theorem commitRecovery_step_splice_support (focal : Player)
    (mine others : CommitRecoveryState setup.program)
    (mineTrace : setup.commitRecoveryProtocol.Trace (some mine))
    (metadata : mine.MetadataEq others)
    (before : ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program mine.point) =
      ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program others.point))
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (leftNext rightNext : CommitRecoveryState setup.program)
    (leftSupport : leftNext ∈ (mine.step leftJoint).support)
    (rightSupport : rightNext ∈ (others.step rightJoint).support)
    (publicNext : setup.attemptPublicSignal focal (some leftNext) =
      setup.attemptPublicSignal focal (some rightNext)) :
    CommitRecoveryState.splice focal leftNext rightNext ∈
      ((CommitRecoveryState.splice focal mine others).step
        (Function.update rightJoint focal (leftJoint focal))).support := by
  obtain ⟨left, leftRaw, rfl⟩ := mine.step_raw_result leftJoint leftNext leftSupport
  obtain ⟨right, rightRaw, rfl⟩ := others.step_raw_result rightJoint rightNext rightSupport
  have exclusions : left.1.2 = right.1.2 := by
    have given := congrArg (fun signal => signal.2.1) publicNext
    simpa only [attemptPublicSignal, commitRecoveryPublic, CommitRecoveryState.close_excluded,
      CommitRecoveryState.install] using given
  have rightMember : right.1 ∈
      (ProtocolState.recoveryStep setup.program others.point mine.excluded rightJoint).support := by
    simpa only [metadata.2.2.1] using rightRaw
  have after : ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program left.1.1) =
      ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program right.1.1) := by
    by_cases committing : ProtocolState.atCommit setup.program mine.point = true
    · exact (ProtocolState.recoveryStep_commit_public_congr focal setup.program
        mine.point others.point before committing mine.excluded leftJoint rightJoint
          left.1 leftRaw right.1 rightMember).1
    · have notCommit : ProtocolState.atCommit setup.program mine.point = false :=
        Bool.eq_false_iff.mpr committing
      have savedNotCommit : ProtocolState.atCommit setup.program mine.saved = false := by
        rw [(setup.commitRecovery_blockFrontier mineTrace).saved_eq_point_of_not_atCommit notCommit,
          notCommit]
      have othersSavedNotCommit : ProtocolState.atCommit setup.program others.saved = false := by
        rw [← (ProtocolState.MetadataEq.controls setup.program mine.saved others.saved
          metadata.2.1).2.1]
        exact savedNotCommit
      rw [setup.installed_close_of_not_committing mine savedNotCommit,
        setup.installed_close_of_not_committing others othersSavedNotCommit] at publicNext
      exact Option.some.inj (congrArg Prod.fst publicNext)
  exact CommitRecoveryState.step_splice_support_of_raw focal mine others metadata before
    leftJoint rightJoint left right leftRaw rightRaw exclusions after

end Setup

end Vegas.SourceProgram
