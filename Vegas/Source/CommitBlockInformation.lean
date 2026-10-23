/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryLift

/-! # Foreign information during a hidden commitment block -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

/-- Two configurations give every player other than the focal owner the same
complete source view. The focal hidden bindings may differ arbitrarily. -/
def ForeignViews {Γ : SourceCtx Player L} (who : Player)
    (first second : Config Player L Γ) : Prop :=
  ∀ observer, observer ≠ who → first.view observer = second.view observer

omit [IExpr.ResultTypes L] in
theorem view_commit_congr {Γ : SourceCtx Player L} {owner observer : Player}
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (first second : Config Player L Γ) (before : first.view observer = second.view observer)
    (left right : PublicationResult (L.Val payload)) (same : owner = observer → left = right) :
    (commitSuccessor name guard first left).view observer =
      (commitSuccessor name guard second right).view observer := by
  apply Prod.ext
  · apply congrArg SourceObservation.mk
    funext cellName cell member
    cases member with
    | here =>
        change (if owner = observer then some left else none) =
          (if owner = observer then some right else none)
        by_cases own : owner = observer
        · simp only [own, ↓reduceIte, same own]
        · simp only [own, ↓reduceIte]
    | there member =>
        have previous := congrArg
          (fun view : DecisionView observer Γ => view.1.cells cellName cell member) before
        cases cell <;> exact previous
  · by_cases own : owner = observer
    · subst observer
      simp only [Config.view, commitSuccessor, Function.update_self]
      have past : first.history owner = second.history owner := congrArg Prod.snd before
      rw [past, same rfl]
    · simp only [Config.view, commitSuccessor, Function.update_of_ne (Ne.symm own)]
      exact congrArg Prod.snd before

omit [IExpr.ResultTypes L] in
theorem ForeignViews.commit {Γ : SourceCtx Player L} {who owner : Player}
    {first second : Config Player L Γ} (related : ForeignViews who first second)
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (left right : PublicationResult (L.Val payload)) (same : owner ≠ who → left = right) :
    ForeignViews who (commitSuccessor name guard first left)
      (commitSuccessor name guard second right) := by
  intro observer foreign
  exact view_commit_congr name guard first second (related observer foreign) left right
    (fun own => same (own.symm ▸ foreign))

end Config

namespace ProtocolState

/-- The same source cursor with identical foreign source views. No relation
between the focal owner's hidden commitment values is imposed. -/
def HiddenBindings (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program → Prop
  | _, _, .ret _, first, second => Config.ForeignViews who first second
  | _, _, .sample _ _ _ next, first, second =>
      match first, second with
      | .inl first, .inl second => Config.ForeignViews who first second
      | .inr first, .inr second => HiddenBindings who next first second
      | _, _ => False
  | _, _, .commit _ _ _ _ next, first, second =>
      match first, second with
      | .inl first, .inl second => Config.ForeignViews who first second
      | .inr first, .inr second => HiddenBindings who next first second
      | _, _ => False
  | _, _, .reveal _ _ _ _ _ _ next, first, second =>
      match first, second with
      | .inl first, .inl second => Config.ForeignViews who first second
      | .inr first, .inr second => HiddenBindings who next first second
      | _, _ => False

theorem hiddenBindings_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) {first second : Config Player L Γ}
    (related : Config.ForeignViews who first second) :
    HiddenBindings who program (entry program first) (entry program second) := by
  cases program <;> exact related

theorem hiddenBindings_refl (who : Player) : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program),
    HiddenBindings who program point point
  | _, _, .ret _, _ => fun _ _ => rfl
  | _, _, .sample _ _ _ next, point => by
      cases point with
      | inl _ => exact fun _ _ => rfl
      | inr point => exact hiddenBindings_refl who next point
  | _, _, .commit _ _ _ _ next, point => by
      cases point with
      | inl _ => exact fun _ _ => rfl
      | inr point => exact hiddenBindings_refl who next point
  | _, _, .reveal _ _ _ _ _ _ next, point => by
      cases point with
      | inl _ => exact fun _ _ => rfl
      | inr point => exact hiddenBindings_refl who next point

theorem HiddenBindings.foreign_observe (who observer : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (first second : ProtocolState program), HiddenBindings who program first second →
      observer ≠ who → observe observer program first = observe observer program second
  | _, _, .ret _, _, _, related, foreign => related observer foreign
  | _, _, .sample _ _ _ next, first, second, related, foreign => by
      cases first <;> cases second
      · exact congrArg Sum.inl (related observer foreign)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (foreign_observe who observer next _ _ related foreign)
  | _, _, .commit _ _ _ _ next, first, second, related, foreign => by
      cases first <;> cases second
      · exact congrArg Sum.inl (related observer foreign)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (foreign_observe who observer next _ _ related foreign)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, related, foreign => by
      cases first <;> cases second
      · exact congrArg Sum.inl (related observer foreign)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (foreign_observe who observer next _ _ related foreign)

/-- Before a publication, arbitrary focal bindings can be replaced by any
other bindings while every other player's complete view is retained. -/
theorem HiddenBindings.commit_step (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (first second : ProtocolState program), HiddenBindings who program first second →
      atCommit program first = true →
      (left right : Player → Option (OwnAction Player L)) →
      (∀ observer, observer ≠ who → left observer = right observer) →
      ∀ target ∈ (step program first left).support,
        ∃ image ∈ (step program second right).support, HiddenBindings who program target image
  | _, _, .ret _, _, _, _, active, _, _, _, _, _ => by cases active
  | _, _, .sample _ _ _ next, first, second, related, active, left, right, same,
      target, reached => by
      cases first with
      | inl _ => cases active
      | inr first =>
          cases second with
          | inl _ => exact related.elim
          | inr second =>
              simp only [step, Sum.elim_inr] at reached ⊢
              rw [PMF.support_map] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨image, supported, relation⟩ :=
                commit_step who next first second related active left right same target reached
              exact ⟨Sum.inr image,
                (PMF.mem_support_map_iff _ _ _).mpr ⟨image, supported, rfl⟩, relation⟩
  | _, _, .commit name owner _ guard next, first, second, related, active, left, right, same,
      target, reached => by
      cases first with
      | inl first =>
          cases second with
          | inr _ => exact related.elim
          | inl second =>
              have equality := (PMF.mem_support_pure_iff _ _).mp reached
              subst target
              refine ⟨_, (PMF.mem_support_pure_iff _ _).mpr rfl, ?_⟩
              apply hiddenBindings_entry
              exact related.commit name guard _ _ (fun foreign => congrArg _ (same owner foreign))
      | inr first =>
          cases second with
          | inl _ => exact related.elim
          | inr second =>
              simp only [step, Sum.elim_inr] at reached ⊢
              rw [PMF.support_map] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨image, supported, relation⟩ :=
                commit_step who next first second related active left right same target reached
              exact ⟨Sum.inr image,
                (PMF.mem_support_map_iff _ _ _).mpr ⟨image, supported, rfl⟩, relation⟩
  | _, _, .reveal _ _ _ _ _ _ next, first, second, related, active, left, right, same,
      target, reached => by
      cases first with
      | inl _ => cases active
      | inr first =>
          cases second with
          | inl _ => exact related.elim
          | inr second =>
              simp only [step, Sum.elim_inr] at reached ⊢
              rw [PMF.support_map] at reached
              obtain ⟨target, reached, rfl⟩ := reached
              obtain ⟨image, supported, relation⟩ :=
                commit_step who next first second related active left right same target reached
              exact ⟨Sum.inr image,
                (PMF.mem_support_map_iff _ _ _).mpr ⟨image, supported, rfl⟩, relation⟩

/-- A hidden focal binding can always be replaced by a legal intended binding.
All supplied foreign intended choices remain literally the same actions. -/
theorem HiddenBindings.intended_commit {Γ : SourceCtx Player L} {O : Finset VarId}
    {who : Player} {program : SourceProgram Player L Γ O}
    {first second : ProtocolState program} (related : HiddenBindings who program first second)
    (active : atCommit program first = true) (left : Player → Option (OwnAction Player L))
    (foreign : ∀ observer, observer ≠ who →
      ProtocolView.intendedMenu observer program (observe observer program first) (left observer))
    (target : ProtocolState program) (reached : target ∈ (step program first left).support) :
    ∃ right : Player → Option (OwnAction Player L),
      (∀ observer, observer ≠ who → left observer = right observer) ∧
      (∀ observer, ProtocolView.intendedMenu observer program
        (observe observer program second) (right observer)) ∧
      ∃ image ∈ (step program second right).support, HiddenBindings who program target image := by
  classical
  obtain ⟨honest, honestLegal⟩ := intendedProgress program second
  let right := Function.update left who (honest who)
  have same (observer : Player) (different : observer ≠ who) :
      left observer = right observer := (Function.update_of_ne different ..).symm
  refine ⟨right, same, ?_, related.commit_step who program first second active
    left right same target reached⟩
  intro observer
  by_cases own : observer = who
  · subst observer
    simpa only [right, Function.update_self] using honestLegal who
  · rw [← same observer own, ← related.foreign_observe who observer program first second own]
    exact foreign observer own

/-- A commitment block has no reveal-side exclusion. With no actual omission,
even an accepted unusable or guard-invalid binding has the ordinary typed law. -/
theorem recoveryStep_commit_joint : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (joint : Player → Option (CommitRecoveryMove Player L)), atCommit program point = true →
    (∀ who, CommitRecoveryMove.missed (joint who) = false) →
    recoveryStep program point ∅ joint =
      (step program point (fun who => (joint who).map (·.action))).map
        (fun target => (target, ∅))
  | _, _, .ret _, _, _, active, _ => by cases active
  | _, _, .sample _ _ _ next, point, joint, active, noMiss => by
      cases point with
      | inl _ => cases active
      | inr point =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [recoveryStep_commit_joint next point joint active noMiss,
            PMF.map_comp, PMF.map_comp]
          rfl
  | _, _, .commit _ owner _ _ next, point, joint, active, noMiss => by
      cases point with
      | inl _ => simp [recoveryStep, step, noMiss owner, PMF.pure_map]
      | inr point =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [recoveryStep_commit_joint next point joint active noMiss,
            PMF.map_comp, PMF.map_comp]
          rfl
  | _, _, .reveal _ _ _ _ _ _ next, point, joint, active, noMiss => by
      cases point with
      | inl _ => cases active
      | inr point =>
          simp only [recoveryStep, step, Sum.elim_inr]
          rw [recoveryStep_commit_joint next point joint active noMiss,
            PMF.map_comp, PMF.map_comp]
          rfl

end ProtocolState
end Vegas.SourceProgram
