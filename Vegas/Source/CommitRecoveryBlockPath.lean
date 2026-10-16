/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryInstructions

/-! # Every typed commitment attempt is a path of legal recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

theorem close_eq_self_of_remaining_gt {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (committing : ProtocolState.atCommit program state.saved = true)
    (beforeEnd : ProtocolState.commitEnd program state.saved <
      ProtocolState.remaining program state.point) : state.close = state := by
  have unfinished : ¬ state.Finished := fun finished => by
    have equal := finished.2
    omega
  simp only [close, unfinished, committing, ↓reduceIte]

end CommitRecoveryState

namespace CommitPrefix

theorem Attempt.liftPoint_entry_of_length_zero
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after)
    (suffix : SourceProgram Player L Δ P) (zero : block.length = 0) :
    block.liftPoint suffix (ProtocolState.entry suffix finished) =
      ProtocolState.entry (block.prepend suffix) entry ∧ after = excluded := by
  cases attempt with
  | nil => exact ⟨rfl, rfl⟩
  | active => simp only [length] at zero; omega
  | excluded => simp only [length] at zero; omega

/-- A typed attempt supplies actual legal recovery choices. The saved frontier
is retained while later commitment instructions remain before its saved block
endpoint. The final instruction applies the actual closure, which may simply
retain an unfinished maximal block. -/
theorem Attempt.instructions_closed_lift
    {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) (initial : Config Player L wholeΓ)
    {block : CommitPrefix Γ O Δ P} {entry : Config Player L Γ} {excluded : Finset Player}
    {finished : Config Player L Δ} {after : Finset Player}
    (attempt : block.Attempt entry excluded finished after) :
    ∀ (suffix : SourceProgram Player L Δ P)
      (lift : ProtocolState (block.prepend suffix) → ProtocolState whole),
    (∀ point, ProtocolState.remaining whole (lift point) =
      ProtocolState.remaining (block.prepend suffix) point) →
    (∀ point, ProtocolState.actor whole (lift point) =
      ProtocolState.actor (block.prepend suffix) point) →
    (∀ point who, ProtocolView.recoveryAvailable who whole
      (ProtocolState.observe who whole (lift point)) =
      ProtocolView.recoveryAvailable who (block.prepend suffix)
        (ProtocolState.observe who (block.prepend suffix) point)) →
    (∀ point excluded joint, ProtocolState.recoveryStep whole (lift point) excluded joint =
      (ProtocolState.recoveryStep (block.prepend suffix) point excluded joint).map
        (fun result => (lift result.1, result.2))) →
    ∀ (state : CommitRecoveryState whole)
      (_atEntry : state.point = lift (ProtocolState.entry (block.prepend suffix) entry))
      (stateExcluded : state.excluded = excluded),
    ProtocolState.atCommit whole state.saved = true →
    ProtocolState.commitEnd whole state.saved ≤ instructionCount suffix → 0 < block.length →
    CommitRecoveryState.InstructionPath whole initial attempt.joints state
      (state.install (lift (block.liftPoint suffix (ProtocolState.entry suffix finished)), after)
        (fun _ member => attempt.excluded_subset (stateExcluded ▸ member))).close := by
  induction attempt with
  | nil =>
      intro suffix lift ranks actors menus steps state atEntry stateExcluded committing endpoint
        positive
      cases positive
  | @active Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      active choice missed missingFailure later ih =>
      intro suffix lift ranks actors menus steps state atEntry stateExcluded committing endpoint
        positive
      let headConfig := commitSuccessor name guard entry choice
      let headExcluded := excludeCommit excluded owner missed
      obtain ⟨monotone, firstLegal, firstReached⟩ := lifted_commit_successor whole initial guard
        (rest.prepend suffix) lift ranks actors menus steps entry state atEntry choice missed
        missingFailure
      have monotone' : state.excluded ⊆ headExcluded := by
        simpa only [stateExcluded, active, ↓reduceIte, headExcluded] using monotone
      let next := state.install (lift (Sum.inr
        (ProtocolState.entry (rest.prepend suffix) headConfig)), headExcluded) monotone'
      have jointEq : state.commitJoint owner name payload choice missed =
          (fun who => if who = owner then some ⟨.commit owner name payload choice, missed⟩
            else none) := by
        funext who
        simp only [CommitRecoveryState.commitJoint, stateExcluded, active, not_false_eq_true,
          and_true]
      have firstStep : next.close ∈
          ((commitRecoveryProtocol whole initial).step state
            ⟨state.commitJoint owner name payload choice missed, firstLegal⟩).support := by
        simpa only [stateExcluded, active, ↓reduceIte, headConfig, headExcluded, next]
          using firstReached
      simp only [Attempt.joints]
      rw [← jointEq]
      by_cases remaining : 0 < rest.length
      · have beforeEnd : ProtocolState.commitEnd whole next.saved <
            ProtocolState.remaining whole next.point := by
          change ProtocolState.commitEnd whole state.saved <
            ProtocolState.remaining whole (lift (Sum.inr _))
          rw [ranks]
          simp only [prepend, ProtocolState.remaining, Sum.elim_inr,
            ProtocolState.remaining_entry]
          rw [instructionCount_prepend]
          omega
        have noClose := next.close_eq_self_of_remaining_gt committing beforeEnd
        rw [noClose] at firstStep
        have continuation := ih suffix (fun point => lift (Sum.inr point))
          (fun point => ranks (Sum.inr point)) (fun point => actors (Sum.inr point))
          (fun point who => menus (Sum.inr point) who)
          (fun point owners joint => by
            simpa only [prepend, ProtocolState.recoveryStep, Sum.elim_inr, PMF.map_comp,
              Function.comp_def] using steps (Sum.inr point) owners joint)
          next rfl rfl committing endpoint remaining
        exact CommitRecoveryState.InstructionPath.step firstLegal firstStep (by
          simpa only [next, CommitRecoveryState.install, liftPoint] using continuation)
      · have zero : rest.length = 0 := by omega
        obtain ⟨point, owners⟩ := later.liftPoint_entry_of_length_zero suffix zero
        have final :
            (state.install (lift ((commit name owner fresh guard rest).liftPoint suffix
              (ProtocolState.entry suffix finished)), after)
              (fun _ member => Attempt.excluded_subset
                (Attempt.active (fresh := fresh) active choice missed missingFailure later)
                  (stateExcluded ▸ member))).close = next.close := by
          simp only [liftPoint, point, owners, next, headConfig, headExcluded]
        rw [final]
        simp only [later.joints_eq_nil_of_length_zero zero]
        exact CommitRecoveryState.InstructionPath.step firstLegal firstStep (.refl _)
  | @excluded Γ Δ O P name owner payload fresh guard rest entry excluded finished after
      inactive later ih =>
      intro suffix lift ranks actors menus steps state atEntry stateExcluded committing endpoint
        positive
      let headConfig := automaticCommit name owner payload entry
      obtain ⟨monotone, firstLegal, firstReached⟩ := lifted_commit_successor whole initial guard
        (rest.prepend suffix) lift ranks actors menus steps entry state atEntry .failure false
        (by intro impossible; cases impossible)
      have monotone' : state.excluded ⊆ excluded := by rw [stateExcluded]
      let next := state.install (lift (Sum.inr
        (ProtocolState.entry (rest.prepend suffix) headConfig)), excluded) monotone'
      have jointEq : state.commitJoint owner name payload .failure false =
          (fun _ => none) := by
        funext who
        simp only [CommitRecoveryState.commitJoint, stateExcluded, inactive, not_true_eq_false,
          and_false, ↓reduceIte]
      have firstStep : next.close ∈
          ((commitRecoveryProtocol whole initial).step state
            ⟨state.commitJoint owner name payload .failure false, firstLegal⟩).support := by
        simpa only [stateExcluded, inactive, ↓reduceIte, headConfig, next] using firstReached
      simp only [Attempt.joints]
      rw [← jointEq]
      by_cases remaining : 0 < rest.length
      · have beforeEnd : ProtocolState.commitEnd whole next.saved <
            ProtocolState.remaining whole next.point := by
          change ProtocolState.commitEnd whole state.saved <
            ProtocolState.remaining whole (lift (Sum.inr _))
          rw [ranks]
          simp only [prepend, ProtocolState.remaining, Sum.elim_inr,
            ProtocolState.remaining_entry]
          rw [instructionCount_prepend]
          omega
        have noClose := next.close_eq_self_of_remaining_gt committing beforeEnd
        rw [noClose] at firstStep
        have continuation := ih suffix (fun point => lift (Sum.inr point))
          (fun point => ranks (Sum.inr point)) (fun point => actors (Sum.inr point))
          (fun point who => menus (Sum.inr point) who)
          (fun point owners joint => by
            simpa only [prepend, ProtocolState.recoveryStep, Sum.elim_inr, PMF.map_comp,
              Function.comp_def] using steps (Sum.inr point) owners joint)
          next rfl rfl committing endpoint remaining
        exact CommitRecoveryState.InstructionPath.step firstLegal firstStep (by
          simpa only [next, CommitRecoveryState.install, liftPoint] using continuation)
      · have zero : rest.length = 0 := by omega
        obtain ⟨point, owners⟩ := later.liftPoint_entry_of_length_zero suffix zero
        have final :
            (state.install (lift ((commit name owner fresh guard rest).liftPoint suffix
              (ProtocolState.entry suffix finished)), after)
              (fun _ member => Attempt.excluded_subset
                (Attempt.excluded (fresh := fresh) (guard := guard) inactive later)
                (stateExcluded ▸ member))).close = next.close := by
          simp only [liftPoint, point, owners, next, headConfig]
        rw [final]
        simp only [later.joints_eq_nil_of_length_zero zero]
        exact CommitRecoveryState.InstructionPath.step firstLegal firstStep (.refl _)

end CommitPrefix
end Vegas.SourceProgram
