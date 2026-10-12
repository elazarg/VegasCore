/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedPlay

/-! # Exclusion after an own failure

A player is excluded at a source position once one of its own events has
failed: a commitment cell of its own holds a failed binding, or a publication
written by one of its reveals failed, whether by withholding or by a rejected
guard (`Vegas.SourceProgram.ProtocolState.Excluded`). Exclusion is a function of
the player's own view (`Vegas.SourceProgram.ProtocolState.excluded_iff_of_observe_eq`):
its commitment cells and every publication are visible to it. No position of
the intended game excludes anyone
(`Vegas.SourceProgram.ProtocolState.not_excluded_of_intended`).

A failure action fails the event it is taken at: a failed binding at a commit
and withholding at a reveal (`Vegas.SourceProgram.OwnAction.IsFailure`). Under
full forfeiture admission every view offers a legal choice that is no action or
a failure action (`Vegas.SourceProgram.ProtocolView.exists_failure_menu`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A failure action: a failed binding at a commit, or withholding at a
reveal. -/
def OwnAction.IsFailure : OwnAction Player L → Prop
  | .commit _ _ _ choice => choice = .failure
  | .reveal _ _ disclose => disclose = false

/-- A commitment cell of `who` holds a failed binding. -/
def FailedCommitment {Γ : SourceCtx Player L} (who : Player) (state : State L Γ) : Prop :=
  ∃ (name : VarId) (payload : L.Ty) (cell : HasVar Γ name (.commitment who payload)),
    state.get cell = .failure

section Observation

variable {Γ : SourceCtx Player L}

omit [IExpr.ResultTypes L] in
theorem sourceObserve_publication_eq {who : Player} {left right : State L Γ}
    (same : sourceObserve who left = sourceObserve who right) {name : VarId} {payload : L.Ty}
    (cell : HasVar Γ name (.publication payload)) : left.get cell = right.get cell :=
  congrArg (fun observation => observation.cells name (.publication payload) cell) same

omit [IExpr.ResultTypes L] in
theorem sourceObserve_ownCommitment_eq {who : Player} {left right : State L Γ}
    (same : sourceObserve who left = sourceObserve who right) {name : VarId} {payload : L.Ty}
    (cell : HasVar Γ name (.commitment who payload)) : left.get cell = right.get cell := by
  have seen := congrArg (fun observation => observation.cells name (.commitment who payload) cell)
    same
  simp only [sourceObserve_commitment, ite_true] at seen
  exact Option.some.inj seen

omit [IExpr.ResultTypes L] in
/-- Whether a player's own binding failed is visible to it. -/
theorem failedCommitment_iff_of_sourceObserve_eq {who : Player} {left right : State L Γ}
    (same : sourceObserve who left = sourceObserve who right) :
    FailedCommitment who left ↔ FailedCommitment who right := by
  constructor <;> rintro ⟨name, payload, cell, failed⟩ <;> refine ⟨name, payload, cell, ?_⟩
  · rw [← sourceObserve_ownCommitment_eq same cell]
    exact failed
  · rw [sourceObserve_ownCommitment_eq same cell]
    exact failed

omit [IExpr.ResultTypes L] in
/-- Dropping the newest cell keeps observations equal. -/
theorem sourceObserve_tail_eq {who : Player} {name : VarId} {cell : CellTy Player L}
    {left right : State L ((name, cell) :: Γ)}
    (same : sourceObserve who left = sourceObserve who right) :
    sourceObserve who (fun _ _ member => left.get (.there member) : State L Γ) =
      sourceObserve who (fun _ _ member => right.get (.there member) : State L Γ) := by
  have cells := congrArg SourceObservation.cells same
  apply congrArg SourceObservation.mk
  funext x kind member
  have seen := congrFun (congrFun (congrFun cells x) kind) (.there member)
  cases kind <;> exact seen

end Observation

namespace ProtocolState

/-- A program point at which `who` is excluded: a commitment cell of its own
holds a failed binding, or a publication written by one of its reveals
failed. -/
def Excluded (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun config => FailedCommitment who config.state
  | _, _, .sample _ _ _ next =>
      Sum.elim (fun config => FailedCommitment who config.state) (Excluded who next)
  | _, _, .commit _ _ _ _ next =>
      Sum.elim (fun config => FailedCommitment who config.state) (Excluded who next)
  | _, _, .reveal _ owner _ _ _ _ next =>
      Sum.elim (fun config => FailedCommitment who config.state)
        (fun rest => (owner = who ∧ (base next rest).get .here = .failure) ∨
          Excluded who next rest)

/-- A player's view determines what it observes of the cells of the program
point's entry context. -/
theorem sourceObserve_base_eq_of_observe_eq (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    observe who program left = observe who program right →
      sourceObserve who (base program left) = sourceObserve who (base program right)
  | _, _, .ret _, _, _, same => congrArg Prod.fst same
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact congrArg Prod.fst (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observe_eq who next first second (Sum.inr.inj same))
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact congrArg Prod.fst (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observe_eq who next first second (Sum.inr.inj same))
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact congrArg Prod.fst (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observe_eq who next first second (Sum.inr.inj same))

/-- **Exclusion is observed.** Whether `who` is excluded is a function of its
view. -/
theorem excluded_iff_of_observe_eq (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    observe who program left = observe who program right →
      (Excluded who program left ↔ Excluded who program right)
  | _, _, .ret _, _, _, same =>
      failedCommitment_iff_of_sourceObserve_eq (congrArg Prod.fst same)
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second =>
              exact failedCommitment_iff_of_sourceObserve_eq
                (congrArg Prod.fst (Sum.inl.inj same))
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second => exact excluded_iff_of_observe_eq who next first second (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second =>
              exact failedCommitment_iff_of_sourceObserve_eq
                (congrArg Prod.fst (Sum.inl.inj same))
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second => exact excluded_iff_of_observe_eq who next first second (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second =>
              exact failedCommitment_iff_of_sourceObserve_eq
                (congrArg Prod.fst (Sum.inl.inj same))
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              have later := Sum.inr.inj same
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observe_eq who next first second later) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, excluded_iff_of_observe_eq who next first second later]

omit [IExpr.ResultTypes L] in
theorem not_failedCommitment_of_intended {Γ : SourceCtx Player L} {unresolved : Finset VarId}
    {config : Config Player L Γ} (intended : config.Intended unresolved) (who : Player) :
    ¬ FailedCommitment who config.state := by
  rintro ⟨_, _, cell, failed⟩
  obtain ⟨value, bound⟩ := intended.bound cell
  rw [bound] at failed
  cases failed

/-- No position of the intended game excludes anyone. -/
theorem not_excluded_of_intended (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Intended program state → ¬ Excluded who program state
  | _, _, .ret _, _, intended => not_failedCommitment_of_intended intended who
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact not_failedCommitment_of_intended intended.1 who
      | inr rest => exact not_excluded_of_intended who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact not_failedCommitment_of_intended intended.1 who
      | inr rest => exact not_excluded_of_intended who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact not_failedCommitment_of_intended intended.1 who
      | inr rest =>
          obtain ⟨⟨value, opened⟩, later⟩ := intended
          rintro (⟨_, failed⟩ | excluded)
          · change (base next rest).get .here = .failure at failed
            rw [opened] at failed
            cases failed
          · exact not_excluded_of_intended who next rest later excluded

end ProtocolState

/-- Under full forfeiture admission every view offers a legal choice that is no
action or a failure action. -/
theorem ProtocolView.exists_failure_menu (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (∀ site, admission site = .forfeiture) → (view : ProtocolView who program) →
      ∃ choice, ProtocolView.menu who program admission view choice ∧
        ∀ action, choice = some action → action.IsFailure
  | _, _, .ret _, _, _, _ =>
      ⟨none, by simp [ProtocolView.menu, ProtocolView.actor], fun _ chosen => by cases chosen⟩
  | _, _, .sample _ _ _ next, admission, forfeits, view => by
      cases view with
      | inl _ =>
          exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor],
            fun _ chosen => by cases chosen⟩
      | inr later => exact exists_failure_menu who next admission forfeits later
  | _, _, .commit (payload := payload) name owner _ _ next, admission, forfeits, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · refine ⟨some (.commit owner name payload .failure), ?_, ?_⟩
            · refine ⟨by simp [ProtocolView.actor, own], .failure, ?_, rfl⟩
              exact (CommitmentAdmission.admits_failure _).mpr (forfeits none)
            · rintro _ ⟨⟩
              rfl
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own],
              fun _ chosen => by cases chosen⟩
      | inr later =>
          exact exists_failure_menu who next (fun site => admission (some site))
            (fun site => forfeits (some site)) later
  | _, _, .reveal _ owner name _ _ _ next, admission, forfeits, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · refine ⟨some (.reveal owner name false), ⟨by simp [ProtocolView.actor, own],
              false, rfl⟩, ?_⟩
            rintro _ ⟨⟩
            rfl
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own],
              fun _ chosen => by cases chosen⟩
      | inr later => exact exists_failure_menu who next admission forfeits later

end Vegas.SourceProgram
