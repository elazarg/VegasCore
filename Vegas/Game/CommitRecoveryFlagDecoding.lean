/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryNormalizedFlagPlan

/-! # Actual source failure classes from the initialized occurrence flags

Omission and accepted failed binding are read from the original flag table,
independently of the chosen domain table. No equality of failure rates is
used as a substitute for equality of the sampled flags.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem inactive_choice (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who info)
    (inactive : ¬ setup.commitRecoveryActive who info.1.1) : choice.val = none := by
  cases selected : choice.val with
  | none => rfl
  | some move =>
      have legal := choice.property
      change setup.commitRecoveryMenu who info choice.val at legal
      rw [selected] at legal
      exact (inactive legal.1).elim

private theorem active_choice (who : Player) (info : setup.commitRecoveryModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who info)
    (active : setup.commitRecoveryActive who info.1.1) :
    ∃ move, choice.val = some move := by
  cases selected : choice.val with
  | none =>
      have legal := choice.property
      change setup.commitRecoveryMenu who info choice.val at legal
      rw [selected] at legal
      exact (legal active).elim
  | some move => exact ⟨move, rfl⟩

/-- At an active binding, the original omission flag is exactly the missing
bit, and either original flag is exactly an unusable accepted-or-missing move.
The domain coordinate cannot manufacture a failed action. -/
theorem commitRecoveryValueFlags_binding_spec (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (omitted bad : Bool) (value : setup.CommitRecoveryValueChoice who info)
    (move : CommitRecoveryMove Player L)
    (selected : (setup.commitRecoveryValueFlags who info omitted bad value).val = some move) :
    move.missing = omitted ∧ (move.action.IsFailure ↔ omitted = true ∨ bad = true) := by
  cases omitted with
  | false =>
      cases bad with
      | false =>
          have chosen : value.val.val = some move := by
            simpa only [commitRecoveryValueFlags, Bool.false_eq_true, Bool.and_false,
              ↓reduceIte] using selected
          have valid := value.property move chosen
          exact ⟨valid.1, by simp only [valid.2, Bool.false_eq_true, or_self]⟩
      | true =>
          have chosen : (setup.commitRecoveryFailureChoice who info false).val = some move := by
            simpa only [commitRecoveryValueFlags, Bool.false_eq_true, committing,
              Bool.true_and, ↓reduceIte] using selected
          have failed := setup.commitRecoveryFailureChoice_spec who info false move chosen
          exact ⟨by simpa only [Bool.and_false] using failed.2,
            by simp only [failed.1, Bool.false_eq_true, or_true]⟩
  | true =>
      have chosen : (setup.commitRecoveryFailureChoice who info true).val = some move := by
        simpa only [commitRecoveryValueFlags, ↓reduceIte] using selected
      have failed := setup.commitRecoveryFailureChoice_spec who info true move chosen
      exact ⟨by simpa only [committing, Bool.and_self] using failed.2,
        by simp only [failed.1, true_or]⟩

private theorem normalized_commit (who : Player)
    (info : setup.commitRecoveryModel.InfoState who)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryNoMissInformation who info)).1.1.1.elim false
        (ProtocolView.atCommit who setup.program) = true := by
  have view : (setup.commitRecoveryNoMissInformation who info).1.1.1 = info.1.1.1 := by
    unfold commitRecoveryNoMissInformation
    split
    · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ info).1
    · rfl
  change ((setup.commitRecoveryNoMissInformation who info).1.1.1.map
    (ProtocolView.eraseHistory who setup.program)).elim false
      (ProtocolView.atCommit who setup.program) = true
  rw [view]
  cases current : info.1.1.1 with
  | none => simp only [current, Option.elim_none, Bool.false_eq_true] at committing
  | some observed =>
      simpa only [Option.map_some, Option.elim_some, ProtocolView.atCommit_eraseHistory,
        current] using committing

private theorem actual_signal (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1 =
      (setup.commitRecoveryPrivate who state, setup.commitRecoveryPublic state) := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  exact setup.commitRecoverySignals_current who trace

private theorem actual_clock (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.2.length = trace.length := by
  have clock := setup.commitRecoveryErasedModel_word_length who trace
  rw [setup.commitRecoveryErasedModel_infoOf] at clock
  simpa only [commitRecoveryErasedInformation, List.length_map] using clock

variable [Fintype Player]

/-- The normalized pure source member reads the two ORIGINAL occurrence flags.
Domain tables may differ arbitrarily; neither failure class changes with them. -/
theorem commitRecoveryNormalizedFlagPolicy_binding_spec
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (memory : setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (info : setup.commitRecoveryModel.InfoState who)
    (committing : info.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (move : CommitRecoveryMove Player L)
    (selected : (setup.commitRecoveryNormalizedFlagPolicy finite who memory info).val = some move) :
    let flags := FiniteAssignment.resolve (fun _ : Nat => (false, false))
      (setup.commitRecoveryFlagSites finite who) memory.1 info.1.2.length
    move.missing = flags.1 ∧ (move.action.IsFailure ↔ flags.1 = true ∨ flags.2 = true) := by
  classical
  let key := setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryNoMissInformation who info)
  let flags := FiniteAssignment.resolve (fun _ : Nat => (false, false))
    (setup.commitRecoveryFlagSites finite who) memory.1 info.1.2.length
  let value := FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
    (setup.commitRecoveryDomainSites finite who) memory.2 key
  have same : (setup.commitRecoveryNormalizedFlagPolicy finite who memory info).val =
      (setup.commitRecoveryValueFlags who key flags.1 flags.2 value).val := by
    change (setup.commitRecoveryFlagPolicy finite who memory key).val = _
    unfold commitRecoveryFlagPolicy
    rw [setup.commitRecoveryNoMissInformation_erased_word_length]
  exact setup.commitRecoveryValueFlags_binding_spec who key
    (setup.normalized_commit who info committing) flags.1 flags.2 value move
    (same.symm.trans selected)

/-- SAME original flags and source clock give SAME omission and accepted-bad
classification across different private domain tables and source queries. -/
theorem commitRecoveryNormalizedFlagPolicy_binding_congr
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (first second :
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (left right : setup.commitRecoveryModel.InfoState who)
    (sameFlags : first.1 = second.1) (sameClock : left.1.2.length = right.1.2.length)
    (leftActive : setup.commitRecoveryActive who left.1.1)
    (rightActive : setup.commitRecoveryActive who right.1.1)
    (leftCommit : left.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (rightCommit : right.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    CommitRecoveryMove.missed
        (setup.commitRecoveryNormalizedFlagPolicy finite who first left).val =
      CommitRecoveryMove.missed
        (setup.commitRecoveryNormalizedFlagPolicy finite who second right).val ∧
    ((∃ move, (setup.commitRecoveryNormalizedFlagPolicy finite who first left).val = some move ∧
        move.action.IsFailure) ↔
      (∃ move, (setup.commitRecoveryNormalizedFlagPolicy finite who second right).val = some move ∧
        move.action.IsFailure)) := by
  obtain ⟨leftMove, leftChosen⟩ := setup.active_choice who left
    (setup.commitRecoveryNormalizedFlagPolicy finite who first left) leftActive
  obtain ⟨rightMove, rightChosen⟩ := setup.active_choice who right
    (setup.commitRecoveryNormalizedFlagPolicy finite who second right) rightActive
  have leftSpec := setup.commitRecoveryNormalizedFlagPolicy_binding_spec finite who first left
    leftCommit leftMove leftChosen
  have rightSpec := setup.commitRecoveryNormalizedFlagPolicy_binding_spec finite who second right
    rightCommit rightMove rightChosen
  dsimp only at leftSpec rightSpec
  rw [sameFlags, sameClock] at leftSpec
  have missing : leftMove.missing = rightMove.missing := leftSpec.1.trans rightSpec.1.symm
  have failed : leftMove.action.IsFailure ↔ rightMove.action.IsFailure :=
    leftSpec.2.trans rightSpec.2.symm
  have omissions : CommitRecoveryMove.missed
        (setup.commitRecoveryNormalizedFlagPolicy finite who first left).val =
      CommitRecoveryMove.missed
        (setup.commitRecoveryNormalizedFlagPolicy finite who second right).val := by
    simpa only [leftChosen, rightChosen, CommitRecoveryMove.missed, Option.elim_some] using missing
  refine ⟨omissions, ?_⟩
  constructor
  · rintro ⟨move, chosen, bad⟩
    have equal := Option.some.inj (leftChosen.symm.trans chosen)
    subst move
    exact ⟨rightMove, rightChosen, failed.mp bad⟩
  · rintro ⟨move, chosen, bad⟩
    have equal := Option.some.inj (rightChosen.symm.trans chosen)
    subst move
    exact ⟨leftMove, leftChosen, failed.mpr bad⟩

/-- Equal ORIGINAL omission coordinates suffice even when accepted-failure
coordinates differ. A voided accepted-failure word is not conditioned away. -/
theorem commitRecoveryNormalizedFlagPolicy_binding_missed_congr
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (first second :
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (left right : setup.commitRecoveryModel.InfoState who)
    (sameOmissions : (fun clock => (first.1 clock).1) = (fun clock => (second.1 clock).1))
    (sameClock : left.1.2.length = right.1.2.length)
    (leftActive : setup.commitRecoveryActive who left.1.1)
    (rightActive : setup.commitRecoveryActive who right.1.1)
    (leftCommit : left.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true)
    (rightCommit : right.1.1.1.elim false (ProtocolView.atCommit who setup.program) = true) :
    CommitRecoveryMove.missed
        (setup.commitRecoveryNormalizedFlagPolicy finite who first left).val =
      CommitRecoveryMove.missed
        (setup.commitRecoveryNormalizedFlagPolicy finite who second right).val := by
  classical
  obtain ⟨leftMove, leftChosen⟩ := setup.active_choice who left
    (setup.commitRecoveryNormalizedFlagPolicy finite who first left) leftActive
  obtain ⟨rightMove, rightChosen⟩ := setup.active_choice who right
    (setup.commitRecoveryNormalizedFlagPolicy finite who second right) rightActive
  have leftSpec := (setup.commitRecoveryNormalizedFlagPolicy_binding_spec finite who first left
    leftCommit leftMove leftChosen).1
  have rightSpec := (setup.commitRecoveryNormalizedFlagPolicy_binding_spec finite who second right
    rightCommit rightMove rightChosen).1
  rw [sameClock] at leftSpec
  have flags : (FiniteAssignment.resolve (fun _ : Nat => (false, false))
        (setup.commitRecoveryFlagSites finite who) first.1 right.1.2.length).1 =
      (FiniteAssignment.resolve (fun _ : Nat => (false, false))
        (setup.commitRecoveryFlagSites finite who) second.1 right.1.2.length).1 := by
    unfold FiniteAssignment.resolve
    split
    · exact congrFun sameOmissions _
    · rfl
  have missing := leftSpec.trans (flags.trans rightSpec.symm)
  simpa only [leftChosen, rightChosen, CommitRecoveryMove.missed, Option.elim_some] using missing

/-- At an actual source commitment step, shared flags determine the entire
omission vector. The source private domain tables can be arbitrary. -/
theorem commitRecoveryNormalizedFlagPolicy_joint_missed_eq
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (firstMemory secondMemory : (who : Player) →
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (flags : ∀ who, (fun clock => ((firstMemory who).1 clock).1) =
      (fun clock => ((secondMemory who).1 clock).1))
    (clock : left.length = right.length) (excluded : first.excluded = second.excluded)
    (observed : ∀ who, ProtocolView.publicOnly who setup.program
      (ProtocolState.observe who setup.program first.point) =
        ProtocolView.publicOnly who setup.program
          (ProtocolState.observe who setup.program second.point))
    (firstCommit : ProtocolState.atCommit setup.program first.point = true)
    (secondCommit : ProtocolState.atCommit setup.program second.point = true) :
    (fun who => CommitRecoveryMove.missed
      (setup.commitRecoveryNormalizedFlagPolicy finite who (firstMemory who)
        (setup.commitRecoveryModel.infoOf who left)).val) =
      (fun who => CommitRecoveryMove.missed
        (setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who)
          (setup.commitRecoveryModel.infoOf who right)).val) := by
  funext who
  have actor : ProtocolState.actor setup.program first.point =
      ProtocolState.actor setup.program second.point := by
    have same := congrArg (ProtocolView.actor who setup.program) (observed who)
    simpa only [ProtocolView.actor_publicOnly, ProtocolState.actor_observe_eq] using same
  have actives : setup.commitRecoveryActive who
        (setup.commitRecoveryModel.infoOf who left).1.1 ↔
      setup.commitRecoveryActive who
        (setup.commitRecoveryModel.infoOf who right).1.1 := by
    rw [setup.actual_signal who left, setup.actual_signal who right]
    simp only [commitRecoveryActive, commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.actor_observe_eq, commitRecoveryPublic, actor, excluded]
  have leftIsCommit : (setup.commitRecoveryModel.infoOf who left).1.1.1.elim false
      (ProtocolView.atCommit who setup.program) = true := by
    rw [setup.actual_signal who left]
    simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe] using firstCommit
  have rightIsCommit : (setup.commitRecoveryModel.infoOf who right).1.1.1.elim false
      (ProtocolView.atCommit who setup.program) = true := by
    rw [setup.actual_signal who right]
    simpa only [commitRecoveryPrivate, Option.map_some, Option.elim_some,
      ProtocolState.atCommit_observe] using secondCommit
  by_cases active : setup.commitRecoveryActive who
      (setup.commitRecoveryModel.infoOf who left).1.1
  · exact (setup.commitRecoveryNormalizedFlagPolicy_binding_missed_congr finite who
      (firstMemory who) (secondMemory who) _ _ (flags who)
      (by rw [setup.actual_clock who left, setup.actual_clock who right, clock])
      active (actives.mp active) leftIsCommit rightIsCommit)
  · rw [setup.inactive_choice who _ _ active,
      setup.inactive_choice who _ _ (fun yes => active (actives.mpr yes))]

/-- The actual original raw source commitment successors have the same
public signal and exclusion set under shared sampled flags, not merely equal
failure rates. Different domain tables include accepted failed bindings. -/
theorem commitRecoveryNormalizedFlagPolicy_raw_public_congr
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (firstMemory secondMemory : (who : Player) →
      setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who)
    (flags : ∀ who, (fun clock => ((firstMemory who).1 clock).1) =
      (fun clock => ((secondMemory who).1 clock).1))
    (clock : left.length = right.length) (excluded : first.excluded = second.excluded)
    (observed : ∀ who, ProtocolView.publicOnly who setup.program
      (ProtocolState.observe who setup.program first.point) =
        ProtocolView.publicOnly who setup.program
          (ProtocolState.observe who setup.program second.point))
    (firstCommit : ProtocolState.atCommit setup.program first.point = true)
    (secondCommit : ProtocolState.atCommit setup.program second.point = true)
    (observer : Player)
    (leftResult rightResult : SourceProgram.ProtocolState setup.program × Finset Player)
    (leftSupport : leftResult ∈ (ProtocolState.recoveryStep setup.program first.point first.excluded
      (fun who => (setup.commitRecoveryNormalizedFlagPolicy finite who (firstMemory who)
        (setup.commitRecoveryModel.infoOf who left)).val)).support)
    (rightSupport : rightResult ∈
      (ProtocolState.recoveryStep setup.program second.point second.excluded
        (fun who => (setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who)
          (setup.commitRecoveryModel.infoOf who right)).val)).support) :
    (∀ who, ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program leftResult.1) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program rightResult.1)) ∧
      leftResult.2 = rightResult.2 := by
  have omissions := setup.commitRecoveryNormalizedFlagPolicy_joint_missed_eq finite first second
    left right firstMemory secondMemory flags clock excluded observed firstCommit secondCommit
  have rightRaw : rightResult ∈
      (ProtocolState.recoveryStep setup.program second.point first.excluded
        (fun who => (setup.commitRecoveryNormalizedFlagPolicy finite who (secondMemory who)
          (setup.commitRecoveryModel.infoOf who right)).val)).support :=
    excluded.symm ▸ rightSupport
  have compared (who : Player) := ProtocolState.recoveryStep_commit_public_congr who setup.program
    first.point second.point (observed who) firstCommit first.excluded _ _
    leftResult leftSupport rightResult rightRaw
  exact ⟨fun who => (compared who).1, (compared observer).2 (congrFun omissions)⟩

end Vegas.SourceProgram.Setup
