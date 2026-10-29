/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.FailedBindingDeviation
import Vegas.Source.Exclusion
import Vegas.Source.AuthenticOpening

/-! # Owing a failure is observed

Whether a player owes a failed reveal is a function of its own view, among the
source points that carry the registry and publication status of their program
point (`Vegas.SourceProgram.ProtocolState.owesFailure_iff_of_observe_eq`). A
failed binding of the player sits in one of its own commitment cells
(`Vegas.SourceProgram.ProtocolState.failedBinding_iff_of_observe_eq`). A debt to a
guard reads the player's own binding, its own observation, and the registry
and publication status, which the program point fixes
(`Vegas.SourceProgram.ProtocolState.indebted_iff_of_observe_eq`). A failed
reveal of the player is a publication, visible to everybody.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Observation

variable {Γ : SourceCtx Player L}

omit [IExpr.ResultTypes L] in
/-- A published result reads only publications, so equal observations read the
same result. -/
theorem Revelation.result_eq_of_sourceObserve_eq {who : Player} {left right : State L Γ}
    (same : sourceObserve who left = sourceObserve who right) {payload : L.Ty}
    (revelation : Revelation Γ payload) : revelation.result left = revelation.result right := by
  cases revelation with
  | unrevealed => rfl
  | revealed cell => exact sourceObserve_publication_eq same cell

omit [IExpr.ResultTypes L] in
/-- Whether `who`'s revealed commitments publish their bindings is visible to
`who`. -/
theorem publishesBindings_iff_of_sourceObserve_eq {who : Player}
    {revelations : Revelations Γ} {left right : State L Γ}
    (same : sourceObserve who left = sourceObserve who right) :
    PublishesBindings who revelations left ↔ PublishesBindings who revelations right := by
  constructor <;> intro publishes x payload cell revealed <;> have kept := publishes cell revealed
  · rwa [Revelation.result_eq_of_sourceObserve_eq same, sourceObserve_ownCommitment_eq same cell]
      at kept
  · rwa [← Revelation.result_eq_of_sourceObserve_eq same,
      ← sourceObserve_ownCommitment_eq same cell] at kept

end Observation

namespace Config

variable {Γ : SourceCtx Player L}

omit [IExpr.ResultTypes L] in
/-- A debt of `who` carries over to a configuration with the same registry,
publication status and observation of `who`. -/
theorem Indebted.of_sourceObserve_eq {who : Player} {unresolved : Finset VarId}
    {left right : Config Player L Γ} (registry : left.registry = right.registry)
    (revelations : @left.revelations = @right.revelations)
    (same : sourceObserve who left.state = sourceObserve who right.state)
    (indebted : left.Indebted who unresolved) : right.Indebted who unresolved := by
  obtain ⟨leftState, leftRegistry, leftRevelations, leftHistory⟩ := left
  obtain ⟨rightState, rightRegistry, rightRevelations, rightHistory⟩ := right
  dsimp only at registry revelations same
  subst registry revelations
  obtain ⟨unique, accounted, publishes, obligation, member, owner, unrevealed, value, bound,
    rejected⟩ := indebted
  obtain ⟨obligationOwner, subject, payload, source, guard⟩ := obligation
  dsimp only at owner
  subst owner
  refine ⟨unique, accounted, (publishesBindings_iff_of_sourceObserve_eq same).mp publishes,
    ⟨obligationOwner, subject, payload, source, guard⟩, member, rfl, unrevealed, value, ?_, ?_⟩
  · rw [← sourceObserve_ownCommitment_eq same source]
    exact bound
  · rw [← same]
    exact rejected

omit [IExpr.ResultTypes L] in
/-- A failed binding of `who` carries over to a configuration with the same
observation of `who`. -/
theorem FailedBinding.of_sourceObserve_eq {who : Player} {unresolved : Finset VarId}
    {left right : Config Player L Γ}
    (same : sourceObserve who left.state = sourceObserve who right.state)
    (failed : left.FailedBinding who unresolved) : right.FailedBinding who unresolved := by
  obtain ⟨unique, name, payload, source, pending, stored⟩ := failed
  refine ⟨unique, name, payload, source, pending, ?_⟩
  rw [← sourceObserve_ownCommitment_eq same source]
  exact stored

end Config

namespace ProtocolState

omit [IExpr.ResultTypes L] in
private theorem config_indebted_iff {who : Player} {Γ : SourceCtx Player L}
    {unresolved : Finset VarId} {registry : Registry Γ} {revelations : Revelations Γ}
    {left right : Config Player L Γ}
    (leftStatic : left.registry = registry ∧ @left.revelations = @revelations)
    (rightStatic : right.registry = registry ∧ @right.revelations = @revelations)
    (same : left.view who = right.view who) :
    left.Indebted who unresolved ↔ right.Indebted who unresolved :=
  have observed := congrArg Prod.fst same
  ⟨Config.Indebted.of_sourceObserve_eq (leftStatic.1.trans rightStatic.1.symm)
      (leftStatic.2.trans rightStatic.2.symm) observed,
    Config.Indebted.of_sourceObserve_eq (rightStatic.1.trans leftStatic.1.symm)
      (rightStatic.2.trans leftStatic.2.symm) observed.symm⟩

omit [IExpr.ResultTypes L] in
private theorem config_failedBinding_iff {who : Player} {Γ : SourceCtx Player L}
    {unresolved : Finset VarId} {left right : Config Player L Γ}
    (same : left.view who = right.view who) :
    left.FailedBinding who unresolved ↔ right.FailedBinding who unresolved :=
  have observed := congrArg Prod.fst same
  ⟨Config.FailedBinding.of_sourceObserve_eq observed,
    Config.FailedBinding.of_sourceObserve_eq observed.symm⟩

/-- **A debt to a guard is observed.** Among source points carrying the
registry and publication status of their program point, whether `who` is
indebted is a function of its view. -/
theorem indebted_iff_of_observe_eq (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (left right : ProtocolState program) →
    StaticAt program registry revelations left → StaticAt program registry revelations right →
    observe who program left = observe who program right →
      (Indebted who program left ↔ Indebted who program right)
  | _, _, .ret _, _, _, _, _, leftStatic, rightStatic, same =>
      config_indebted_iff leftStatic rightStatic same
  | _, _, .sample _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff leftStatic rightStatic (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact indebted_iff_of_observe_eq who next _ _ first second leftStatic rightStatic
                (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff leftStatic rightStatic (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact indebted_iff_of_observe_eq who next _ _ first second leftStatic rightStatic
                (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, _, _, left, right, leftStatic, rightStatic, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_indebted_iff leftStatic rightStatic (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              have later := Sum.inr.inj same
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observe_eq who next first second later) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, indebted_iff_of_observe_eq who next _ _ first second leftStatic
                rightStatic later]

/-- **A failed binding is observed.** Whether `who` holds a failed binding is a
function of its view. -/
theorem failedBinding_iff_of_observe_eq (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    observe who program left = observe who program right →
      (FailedBinding who program left ↔ FailedBinding who program right)
  | _, _, .ret _, _, _, same => config_failedBinding_iff same
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_failedBinding_iff (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact failedBinding_iff_of_observe_eq who next first second (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_failedBinding_iff (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact failedBinding_iff_of_observe_eq who next first second (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact config_failedBinding_iff (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              have later := Sum.inr.inj same
              have published := sourceObserve_publication_eq
                (sourceObserve_base_eq_of_observe_eq who next first second later) .here
              change (_ ∧ _ = _) ∨ _ ↔ (_ ∧ _ = _) ∨ _
              rw [published, failedBinding_iff_of_observe_eq who next first second later]

/-- **Owing a failure is observed.** Among source points carrying the registry
and publication status of their program point, whether `who` owes a failed
reveal is a function of its view. -/
theorem owesFailure_iff_of_observe_eq (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (left right : ProtocolState program)
    (leftStatic : StaticAt program registry revelations left)
    (rightStatic : StaticAt program registry revelations right)
    (same : observe who program left = observe who program right) :
    OwesFailure who program left ↔ OwesFailure who program right :=
  or_congr (indebted_iff_of_observe_eq who program registry revelations left right leftStatic
    rightStatic same) (failedBinding_iff_of_observe_eq who program left right same)

end ProtocolState

end Vegas.SourceProgram
