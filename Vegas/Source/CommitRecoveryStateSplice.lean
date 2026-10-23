/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryConfigSplice
import Vegas.Source.CommitRecoveryMetadata

/-! # Owner substitution on original typed source points

The operation follows the existing source cursor and combines the original
configurations. Derived public metadata rules out its unused mismatched cases.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
/-- Automatic excluded reveals retain the original histories on both sides. -/
theorem splice_automaticReveal {Γ : SourceCtx Player L} {name : VarId}
    {owner : Player} {payload : L.Ty} (focal : Player) (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (mine others : Config Player L Γ) :
    splice focal { revealSuccessor published source mine false with history := mine.history }
        { revealSuccessor published source others false with history := others.history } =
      { revealSuccessor published source (splice focal mine others) false with
        history := (splice focal mine others).history } := by
  unfold splice revealSuccessor
  simp only [Bool.false_eq_true, ↓reduceIte, ite_self]
  congr 1
  funext cellName cell member
  cases member <;> rfl

end Config

namespace ProtocolState

/-- Take the focal owner's cells and action recall from the first original
point and every other component from the second at their common source cursor. -/
def splice (focal : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program →
      ProtocolState program
  | _, _, .ret _, mine, others => Config.splice focal mine others
  | _, _, .sample _ _ _ next, mine, others => match mine, others with
    | .inl mine, .inl others => .inl (Config.splice focal mine others)
    | .inr mine, .inr others => .inr (splice focal next mine others)
    | _, others => others
  | _, _, .commit _ _ _ _ next, mine, others => match mine, others with
    | .inl mine, .inl others => .inl (Config.splice focal mine others)
    | .inr mine, .inr others => .inr (splice focal next mine others)
    | _, others => others
  | _, _, .reveal _ _ _ _ _ _ next, mine, others => match mine, others with
    | .inl mine, .inl others => .inl (Config.splice focal mine others)
    | .inr mine, .inr others => .inr (splice focal next mine others)
    | _, others => others

/-- The actual source entry commutes with combining original configurations. -/
theorem splice_entry {Γ : SourceCtx Player L} {O : Finset VarId} (focal : Player)
    (program : SourceProgram Player L Γ O) (mine others : Config Player L Γ) :
    splice focal program (entry program mine) (entry program others) =
      entry program (Config.splice focal mine others) := by
  cases program <;> rfl

/-- Combining original source points preserves the second point's full static metadata. -/
theorem splice_metadata_eq_others (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      MetadataEq program mine others → MetadataEq program (splice focal program mine others) others
  | _, _, .ret _, _, _, _ => ⟨rfl, rfl⟩
  | _, _, .sample _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact ⟨rfl, rfl⟩
      · cases same
      · cases same
      · exact splice_metadata_eq_others focal next _ _ same
  | _, _, .commit _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact ⟨rfl, rfl⟩
      · cases same
      · cases same
      · exact splice_metadata_eq_others focal next _ _ same
  | _, _, .reveal _ _ _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact ⟨rfl, rfl⟩
      · cases same
      · cases same
      · exact splice_metadata_eq_others focal next _ _ same

/-- Matching public cells retain the focal owner's entire original source view. -/
theorem splice_observe_self (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      ProtocolView.publicOnly focal program (observe focal program mine) =
        ProtocolView.publicOnly focal program (observe focal program others) →
      observe focal program (splice focal program mine others) = observe focal program mine
  | _, _, .ret _, mine, others, same =>
      Config.splice_view_self focal mine others (congrArg Prod.fst same)
  | _, _, .sample _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (Config.splice_view_self focal _ _
          (congrArg Prod.fst (Sum.inl.inj same)))
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_observe_self focal next _ _ (Sum.inr.inj same))
  | _, _, .commit _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (Config.splice_view_self focal _ _
          (congrArg Prod.fst (Sum.inl.inj same)))
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_observe_self focal next _ _ (Sum.inr.inj same))
  | _, _, .reveal _ _ _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (Config.splice_view_self focal _ _
          (congrArg Prod.fst (Sum.inl.inj same)))
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_observe_self focal next _ _ (Sum.inr.inj same))

/-- Each other owner retains its full original source view and private recall. -/
theorem splice_observe_other (focal observer : Player) (foreign : observer ≠ focal) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      MetadataEq program mine others →
        observe observer program (splice focal program mine others) =
          observe observer program others
  | _, _, .ret _, mine, others, _ => Config.splice_view_other focal observer mine others foreign
  | _, _, .sample _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (Config.splice_view_other focal observer _ _ foreign)
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_observe_other focal observer foreign next _ _ same)
  | _, _, .commit _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (Config.splice_view_other focal observer _ _ foreign)
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_observe_other focal observer foreign next _ _ same)
  | _, _, .reveal _ _ _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · exact congrArg Sum.inl (Config.splice_view_other focal observer _ _ foreign)
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_observe_other focal observer foreign next _ _ same)

/-- Original action recall is combined owner by owner, never restarted on entry. -/
theorem history_splice (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      MetadataEq program mine others →
        history program (splice focal program mine others) =
          Function.update (history program others) focal (history program mine focal)
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact history_splice focal next _ _ same
  | _, _, .commit _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact history_splice focal next _ _ same
  | _, _, .reveal _ _ _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact history_splice focal next _ _ same

/-- Restoring original action words commutes with the same owner substitution. -/
theorem splice_withHistory (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      MetadataEq program mine others → ∀ left right : History Player L,
        splice focal program (withHistory program mine left) (withHistory program others right) =
          withHistory program (splice focal program mine others)
            (Function.update right focal (left focal))
  | _, _, .ret _, _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, mine, others, same, left, right => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_withHistory focal next _ _ same left right)
  | _, _, .commit _ _ _ _ next, mine, others, same, left, right => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_withHistory focal next _ _ same left right)
  | _, _, .reveal _ _ _ _ _ _ next, mine, others, same, left, right => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_withHistory focal next _ _ same left right)

/-- Exhausting an actual commitment block commutes with owner substitution. -/
theorem splice_automaticCommitBlock (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (mine others : ProtocolState program),
      MetadataEq program mine others →
        splice focal program (automaticCommitBlock program mine)
            (automaticCommitBlock program others) =
          automaticCommitBlock program (splice focal program mine others)
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_automaticCommitBlock focal next _ _ same)
  | _, _, .commit (payload := payload) name owner _ _ next, mine, others, same => by
      cases mine with
      | inl mine =>
          cases others with
          | inr _ => cases same
          | inl others =>
              have related : Config.MetadataEq (automaticCommit name owner payload mine)
                  (automaticCommit name owner payload others) :=
                ⟨congrArg Registry.weaken same.1, congrArg Revelations.weaken same.2⟩
              have continuation := splice_automaticCommitBlock focal next _ _
                (metadata_entry next _ _ related)
              simp only [splice_entry, Config.splice_automaticCommit] at continuation
              exact congrArg Sum.inr continuation
      | inr mine =>
          cases others with
          | inl _ => cases same
          | inr others =>
              exact congrArg Sum.inr (splice_automaticCommitBlock focal next mine others same)
  | _, _, .reveal _ _ _ _ _ _ next, mine, others, same => by
      cases mine <;> cases others
      · rfl
      · cases same
      · cases same
      · exact congrArg Sum.inr (splice_automaticCommitBlock focal next _ _ same)

end ProtocolState

end Vegas.SourceProgram
