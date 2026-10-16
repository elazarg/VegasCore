/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryObservation
import Vegas.Source.CommitRecoveryFrontier
import Vegas.Source.CommitRecoveryNonCommitPath

/-! # Observable public successors of noncommitment recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Sample steps retain exclusions. Reveal steps add exactly the owner of a
failed public publication, so equal next observations determine equal exclusions. -/
theorem recoveryStep_noncommit_excluded_eq (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program)
      (excluded : Finset Player)
      (firstJoint secondJoint : Player → Option (CommitRecoveryMove Player L))
      (firstAfter secondAfter : ProtocolState program × Finset Player),
      atCommit program first = false →
      observe who program first = observe who program second →
      firstAfter ∈ (recoveryStep program first excluded firstJoint).support →
      secondAfter ∈ (recoveryStep program second excluded secondJoint).support →
      observe who program firstAfter.1 = observe who program secondAfter.1 →
      firstAfter.2 = secondAfter.2
  | _, _, .ret _, _, _, _, _, _, _, _, _, _, firstReached, secondReached, _ => by
      cases (PMF.mem_support_pure_iff ..).mp firstReached
      cases (PMF.mem_support_pure_iff ..).mp secondReached
      rfl
  | _, _, .sample _ _ _ next, first, second, excluded, firstJoint, secondJoint,
      firstAfter, secondAfter, notCommit, before, firstReached, secondReached, after => by
      cases first <;> cases second
      · obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstReached
        obtain ⟨_, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondReached
        rfl
      · cases before
      · cases before
      · obtain ⟨left, leftReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstReached
        obtain ⟨right, rightReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondReached
        exact recoveryStep_noncommit_excluded_eq who next _ _ excluded firstJoint secondJoint
          left right notCommit (Sum.inr.inj before) leftReached rightReached (Sum.inr.inj after)
  | _, _, .commit _ _ _ _ next, first, second, excluded, firstJoint, secondJoint,
      firstAfter, secondAfter, notCommit, before, firstReached, secondReached, after => by
      cases first with
      | inl _ => cases notCommit
      | inr first =>
          cases second with
          | inl _ => cases before
          | inr second =>
              obtain ⟨left, leftReached, rfl⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp firstReached
              obtain ⟨right, rightReached, rfl⟩ :=
                (PMF.mem_support_map_iff _ _ _).mp secondReached
              exact recoveryStep_noncommit_excluded_eq who next first second excluded
                firstJoint secondJoint left right notCommit (Sum.inr.inj before)
                  leftReached rightReached (Sum.inr.inj after)
  | _, _, .reveal (payload := payload) published owner _ _ selected _ next,
      first, second, excluded, firstJoint, secondJoint, firstAfter, secondAfter,
      notCommit, before, firstReached, secondReached, after => by
      cases first <;> cases second
      · simp only [recoveryStep, Sum.elim_inl,
          PMF.mem_support_pure_iff] at firstReached secondReached
        subst firstAfter
        subst secondAfter
        dsimp only
        by_cases inactive : owner ∈ excluded
        · split <;> split <;> simp only [Finset.insert_eq_of_mem inactive]
        · have views := congrArg (ProtocolView.entryView who next) (Sum.inr.inj after)
          simp only [ite_eq_right inactive, ProtocolView.entryView_observe_entry] at views
          have result := congrArg
            (fun view : DecisionView who ((published, .publication payload) :: _) =>
              view.1.cells published (.publication payload) .here) views
          simp only [Config.view, sourceObserve_publication] at result
          simp only [ite_eq_right inactive]
          rw [result]
      · cases before
      · cases before
      · obtain ⟨left, leftReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstReached
        obtain ⟨right, rightReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondReached
        exact recoveryStep_noncommit_excluded_eq who next _ _ excluded firstJoint secondJoint
          left right notCommit (Sum.inr.inj before) leftReached rightReached (Sum.inr.inj after)

end ProtocolState

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

end CommitRecoveryState

namespace Setup

/-- At genuine noncommitment instructions, equal before public and private
views and equal next private views determine the full next public signal.
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
    (before : setup.commitRecoveryPrivate who (some first) =
      setup.commitRecoveryPrivate who (some second))
    (publicBefore : setup.commitRecoveryPublic (some first) =
      setup.commitRecoveryPublic (some second))
    (after : setup.commitRecoveryPrivate who firstAfter =
      setup.commitRecoveryPrivate who secondAfter) :
    setup.commitRecoveryPublic firstAfter = setup.commitRecoveryPublic secondAfter := by
  have privateBefore : ProtocolState.observe who setup.program first.point =
      ProtocolState.observe who setup.program second.point := Option.some.inj before
  have exclusions : first.excluded = second.excluded := congrArg Prod.fst publicBefore
  have generation : first.generation = second.generation :=
    congrArg (fun info => info.2.1) publicBefore
  have secondNotCommit : ProtocolState.atCommit setup.program second.point = false := by
    rw [← ProtocolState.atCommit_observe setup.program second.point who, ← privateBefore,
      ProtocolState.atCommit_observe, notCommit]
  obtain ⟨left, leftReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp firstReached
  obtain ⟨right, rightReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp secondReached
  obtain ⟨leftRaw, leftRawReached, rfl⟩ := first.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier firstTrace) notCommit firstJoint left leftReached
  obtain ⟨rightRaw, rightRawReached, rfl⟩ := second.step_noncommit_atPoint
    (setup.commitRecovery_blockFrontier secondTrace) secondNotCommit secondJoint right rightReached
  have privateAfter : ProtocolState.observe who setup.program leftRaw.1 =
      ProtocolState.observe who setup.program rightRaw.1 := Option.some.inj after
  have rawExclusions := ProtocolState.recoveryStep_noncommit_excluded_eq who setup.program
    first.point second.point first.excluded firstJoint secondJoint leftRaw rightRaw
      notCommit privateBefore leftRawReached (exclusions ▸ rightRawReached) privateAfter
  have leftRank := ProtocolView.position_add_remaining who setup.program leftRaw.1
  have rightRank := ProtocolView.position_add_remaining who setup.program rightRaw.1
  rw [privateAfter] at leftRank
  have rank : ProtocolState.remaining setup.program leftRaw.1 =
      ProtocolState.remaining setup.program rightRaw.1 := by omega
  simp only [commitRecoveryPublic, CommitRecoveryState.atPoint, rawExclusions, generation, rank]

end Setup
end Vegas.SourceProgram
