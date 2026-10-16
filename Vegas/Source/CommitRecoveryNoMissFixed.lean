/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNoMissRepresentative

/-! # Actual ordinary source queries and the normalized pool fiber

The original source exclusion scan is monotone. If a genuine extension has
introduced no excluded owner, normalizing that interval changes no signal or
own-play tag. This identifies the ordinary erased class in a normalized pool;
any remaining actual commitment member has a new excluded owner.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- An actual initialized source extension without a new exclusion is fixed
by normalization of that entire interval, including every old own-play tag. -/
theorem commitRecoveryWithAttemptExclusions_fixed_of_prefix (who : Player)
    (entry : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some entry))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (kept : TracePrefix prior trace)
    (unchanged : (setup.commitRecoveryPublic state).1 = entry.excluded) :
    setup.commitRecoveryWithAttemptExclusions who prior.length entry.excluded
      (setup.commitRecoveryModel.infoOf who trace) =
        setup.commitRecoveryModel.infoOf who trace := by
  have grows : ∀ {last : setup.commitRecoveryProtocol.State}
      (later : setup.commitRecoveryProtocol.Trace last) (_prefix : TracePrefix prior later),
      entry.excluded ⊆ (setup.commitRecoveryPublic last).1 := by
    intro last later retained
    induction retained with
    | refl => exact Finset.Subset.refl _
    | extend earlier joint legal reached ih =>
        exact ih.trans (setup.commitRecovery_step_excluded_subset joint legal reached)
  revert unchanged
  induction kept with
  | refl =>
      intro _
      exact setup.commitRecoveryWithAttemptExclusions_at_entry who entry prior
  | @extend before after earlier kept joint legal reached ih =>
      intro unchanged
      have previous : (setup.commitRecoveryPublic before).1 = entry.excluded :=
        Finset.Subset.antisymm (by
          simpa only [unchanged] using
            setup.commitRecovery_step_excluded_subset joint legal reached) (grows earlier kept)
      have information := ih previous
      apply Eq.symm
      apply setup.normalized_information_extend who prior.length entry.excluded
        earlier earlier joint joint legal legal reached reached information.symm rfl
      change (_, _) = (_, if prior.length ≤ earlier.length + 1 then
        (entry.excluded, (setup.commitRecoveryPublic after).2) else _)
      rw [ite_eq_left (kept.length_le.trans (Nat.le_succ _))]
      exact Prod.ext rfl (Prod.ext unchanged rfl)

/-- At every genuine source query with unchanged entry exclusions, the global
no-new-omission representative is literally the original full information. -/
theorem commitRecoveryNoMissInformation_eq_of_unchanged_exclusions (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (unchanged : current.excluded = current.entryExcluded) :
    setup.commitRecoveryNoMissInformation who (setup.commitRecoveryModel.infoOf who trace) =
      setup.commitRecoveryModel.infoOf who trace := by
  by_cases committing : ProtocolState.atCommit setup.program current.point = true
  · obtain ⟨prior, kept, rank⟩ := setup.commitRecovery_attempt_entry current trace committing
    have fixed := setup.commitRecoveryWithAttemptExclusions_fixed_of_prefix who
      (CommitRecoveryState.atPoint current.saved current.entryExcluded current.generation)
      prior trace kept unchanged
    unfold commitRecoveryNoMissInformation
    split
    · rw [setup.commitRecoveryAttemptStart_of_entry who current trace prior kept rank,
        setup.commitRecoverySavedExclusions_of_entry who current trace prior kept rank]
      exact fixed
    · rfl
  · have currentSignal : (setup.commitRecoveryModel.infoOf who trace).1.1 =
        (setup.commitRecoveryPrivate who (some current),
          setup.commitRecoveryPublic (some current)) := by
      change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1 = _
      rw [InfoSignals.withOwnPlayRecall_infoOf, setup.commitRecoverySignals_current who trace]
    unfold commitRecoveryNoMissInformation
    rw [currentSignal]
    simp only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe, committing, Bool.false_eq_true, false_and, ite_false]

/-- Two actual normalized-pool members with no new exclusions belong to the
SAME ordinary erased-information class, using their original initialized
histories. No history, prior or observation identification is assumed. -/
theorem commitRecovery_erased_eq_of_query_eq_of_unchanged_exclusions (who : Player)
    (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (leftUnchanged : first.excluded = first.entryExcluded)
    (rightUnchanged : second.excluded = second.entryExcluded)
    (same : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who (setup.commitRecoveryModel.infoOf who left)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who (setup.commitRecoveryModel.infoOf who right))) :
    setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who left) =
      setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who right) := by
  rwa [setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions
      who first left leftUnchanged,
    setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions
      who second right rightUnchanged] at same

/-- An actual member of an ordinary member's normalized pool either lies in
that SAME ordinary erased class or has genuinely acquired a new exclusion.
This is the actual runtime partition used for the pooled conditional sum. -/
theorem commitRecovery_query_fiber_cases (who : Player)
    (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (leftUnchanged : first.excluded = first.entryExcluded)
    (same : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who (setup.commitRecoveryModel.infoOf who left)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who (setup.commitRecoveryModel.infoOf who right))) :
    setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who left) =
        setup.commitRecoveryErasedInformation who (setup.commitRecoveryModel.infoOf who right) ∨
      second.NewFailure := by
  by_cases rightUnchanged : second.excluded = second.entryExcluded
  · exact Or.inl (setup.commitRecovery_erased_eq_of_query_eq_of_unchanged_exclusions
      who first second left right leftUnchanged rightUnchanged same)
  · apply Or.inr
    apply Finset.sdiff_nonempty.mpr
    intro included
    exact rightUnchanged (Finset.Subset.antisymm included second.entered)

/-- Every actual surviving commitment query has a genuine ordinary member
of its normalized pool, produced by the SAME initialized no-new-miss replay.
The ENTIRE actual pool fiber then consists of that ordinary erased class and
members with a genuinely new excluded owner. -/
theorem commitRecovery_query_fiber_of_history (who : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (survives : who ∉ current.excluded) :
    ∃ ordinary : CommitRecoveryState setup.program,
      ∃ ordinaryTrace : setup.commitRecoveryProtocol.Trace (some ordinary),
        ordinary.excluded = ordinary.entryExcluded ∧
        setup.commitRecoveryErasedInformation who
            (setup.commitRecoveryModel.infoOf who ordinaryTrace) =
          setup.commitRecoveryErasedInformation who
            (setup.commitRecoveryNoMissInformation who
              (setup.commitRecoveryModel.infoOf who trace)) ∧
        ∀ (other : CommitRecoveryState setup.program)
          (otherTrace : setup.commitRecoveryProtocol.Trace (some other)),
          setup.commitRecoveryErasedInformation who
              (setup.commitRecoveryNoMissInformation who
                (setup.commitRecoveryModel.infoOf who trace)) =
            setup.commitRecoveryErasedInformation who
              (setup.commitRecoveryNoMissInformation who
                (setup.commitRecoveryModel.infoOf who otherTrace)) →
          setup.commitRecoveryErasedInformation who
              (setup.commitRecoveryModel.infoOf who ordinaryTrace) =
            setup.commitRecoveryErasedInformation who
              (setup.commitRecoveryModel.infoOf who otherTrace) ∨ other.NewFailure := by
  obtain ⟨ordinary, ordinaryTrace, excluded, entryExcluded, _saved, _generation, _view, info⟩ :=
    setup.commitRecoveryNoMissInformation_genuine who current trace committing survives
  have unchanged : ordinary.excluded = ordinary.entryExcluded :=
    excluded.trans entryExcluded.symm
  have key := congrArg (setup.commitRecoveryErasedInformation who) info
  refine ⟨ordinary, ordinaryTrace, unchanged, key, ?_⟩
  intro other otherTrace same
  apply setup.commitRecovery_query_fiber_cases who ordinary other ordinaryTrace otherTrace unchanged
  rw [setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions
    who ordinary ordinaryTrace unchanged]
  exact key.trans same

end Vegas.SourceProgram.Setup
