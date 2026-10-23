/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.PrivateInputsIndependent
import Vegas.Source.DisclosureAliases
import Vegas.Source.CommitRecoveryPublicSuccessor

/-! # Combining actual owner views in the original source configuration

The existing typed splice takes one owner's private cells from one state
and all remaining cells from another. The same operation on configurations
retains that owner's original recall and the other state's static metadata.
-/

noncomputable section

namespace Vegas.SourceProgram.Config

variable {Player : Type} [DecidableEq Player] {L : IExpr}
  {Γ : SourceCtx Player L}

/-- Combine one owner's typed cells and original action recall with the other
configuration's remaining cells, histories, registry and publication status. -/
def splice (focal : Player) (mine others : Config Player L Γ) : Config Player L Γ :=
  { state := SourceProgram.splice focal mine.state others.state
    registry := others.registry
    revelations := others.revelations
    history := Function.update others.history focal (mine.history focal) }

/-- Matching public cells make the combined focal view exactly its original view. -/
theorem splice_view_self (focal : Player) (mine others : Config Player L Γ)
    (publicCells : (mine.view focal).1.publicOnly = (others.view focal).1.publicOnly) :
    (splice focal mine others).view focal = mine.view focal := by
  apply Prod.ext
  · apply sourceObserve_congr
    · intro cellName cellType member
      exact (congrArg (fun view => view.cells cellName (.publicData cellType) member)
        publicCells).symm
    · intro cellName cellType member
      exact (congrArg (fun view => view.cells cellName (.publication cellType) member)
        publicCells).symm
    · intro cellName cellType member
      change (if (some focal : Option Player) = some focal then mine.state.get member
        else others.state.get member) = mine.state.get member
      exact ite_eq_left rfl
    · intro cellName cellType member
      change (if (some focal : Option Player) = some focal then mine.state.get member
        else others.state.get member) = mine.state.get member
      exact ite_eq_left rfl
  · exact Function.update_self ..

/-- Every other owner's full typed view and original action recall stay literal. -/
theorem splice_view_other (focal observer : Player) (mine others : Config Player L Γ)
    (foreign : observer ≠ focal) :
    (splice focal mine others).view observer = others.view observer := by
  apply Prod.ext
  · apply sourceObserve_congr
    · intro cellName cellType member
      rfl
    · intro cellName cellType member
      rfl
    · intro cellName cellType member
      change (if (some observer : Option Player) = some focal then mine.state.get member
        else others.state.get member) = others.state.get member
      exact ite_eq_right (fun same => foreign (Option.some.inj same))
    · intro cellName cellType member
      change (if (some observer : Option Player) = some focal then mine.state.get member
        else others.state.get member) = others.state.get member
      exact ite_eq_right (fun same => foreign (Option.some.inj same))
  · exact Function.update_of_ne foreign ..

/-- A public sample commutes with the typed splice and keeps its actual draw. -/
theorem splice_sample {payload : L.Ty} (focal : Player) (name : VarId)
    (mine others : Config Player L Γ) (left right : L.Val payload) :
    splice focal (sampleSuccessor name mine left) (sampleSuccessor name others right) =
      sampleSuccessor name (splice focal mine others) right := by
  unfold splice sampleSuccessor
  congr 1
  funext cellName cell member
  cases member <;> rfl

/-- Commitment substitution uses the focal original raw value exactly at its
own instruction; every foreign raw value and history remains unchanged. -/
theorem splice_commit {owner : Player} {payload : L.Ty} (focal : Player) (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (mine others : Config Player L Γ)
    (left right : PublicationResult (L.Val payload)) :
    splice focal (commitSuccessor name guard mine left) (commitSuccessor name guard others right) =
      commitSuccessor name guard (splice focal mine others)
        (if owner = focal then left else right) := by
  unfold splice commitSuccessor
  congr 1
  · funext cellName cell member
    cases member with
    | here =>
        change (if (some owner : Option Player) = some focal then left else right) =
          if owner = focal then left else right
        simp only [Option.some.injEq]
    | there member => rfl
  · funext observer
    by_cases own : owner = focal
    · subst owner
      by_cases selected : observer = focal
      · subst observer
        simp only [Function.update_self, ↓reduceIte]
      · simp only [Function.update_of_ne selected, ↓reduceIte]
    · by_cases selected : observer = focal
      · subst observer
        simp only [Function.update_self, Function.update_of_ne (Ne.symm own)]
      · simp only [Function.update_of_ne selected]
        by_cases acting : observer = owner
        · subst observer
          simp only [Function.update_self, Function.update_of_ne own, ite_eq_right own]
        · simp only [Function.update_of_ne acting, Function.update_of_ne selected]

/-- Excluded automatic bindings splice without adding any owned action. -/
theorem splice_automaticCommit (focal owner : Player) (name : VarId) (payload : L.Ty)
    (mine others : Config Player L Γ) :
    splice focal (automaticCommit name owner payload mine)
        (automaticCommit name owner payload others) =
      automaticCommit name owner payload (splice focal mine others) := by
  unfold splice automaticCommit
  congr 1
  funext cellName cell member
  cases member with
  | here =>
      change (if (some owner : Option Player) = some focal then
          (PublicationResult.failure : PublicationResult (L.Val payload)) else .failure) = .failure
      split <;> rfl
  | there member => rfl

/-- The actual deferred reveal verdict comes from the revealing owner's
original observation and the common derived static metadata. -/
theorem splice_disclosureResult {name : VarId} {owner : Player} {payload : L.Ty}
    (focal : Player) (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (mine others : Config Player L Γ)
    (publicCells : (mine.view focal).1.publicOnly = (others.view focal).1.publicOnly)
    (registry : mine.registry = others.registry)
    (revelations : @mine.revelations = @others.revelations) (left right : Bool) :
    disclosureResult published source (splice focal mine others)
        (if owner = focal then left else right) =
      if owner = focal then disclosureResult published source mine left
      else disclosureResult published source others right := by
  by_cases own : owner = focal
  · subst owner
    simp only [↓reduceIte]
    exact disclosureResult_observation_congr published source (splice focal mine others) mine
      registry.symm revelations.symm
      (congrArg Prod.fst (splice_view_self focal mine others publicCells)) left
  · simp only [own, ↓reduceIte]
    exact disclosureResult_observation_congr published source (splice focal mine others) others
      rfl rfl
      (congrArg Prod.fst (splice_view_other focal owner mine others own)) right

/-- Equal original public publications make the actual reveal commute with
the owner splice, including each original disclosure action in recall. -/
theorem splice_reveal {name : VarId} {owner : Player} {payload : L.Ty}
    (focal : Player) (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (mine others : Config Player L Γ)
    (publicCells : (mine.view focal).1.publicOnly = (others.view focal).1.publicOnly)
    (registry : mine.registry = others.registry)
    (revelations : @mine.revelations = @others.revelations) (left right : Bool)
    (publishedResult : disclosureResult published source mine left =
      disclosureResult published source others right) :
    splice focal (revealSuccessor published source mine left)
        (revealSuccessor published source others right) =
      revealSuccessor published source (splice focal mine others)
        (if owner = focal then left else right) := by
  have result : disclosureResult published source (splice focal mine others)
        (if owner = focal then left else right) =
      disclosureResult published source others right := by
    rw [splice_disclosureResult focal published source mine others publicCells registry
      revelations left right]
    split
    · exact publishedResult
    · rfl
  unfold splice revealSuccessor
  congr 1
  · funext cellName cell member
    cases member with
    | here => exact result.symm
    | there member => rfl
  · funext observer
    by_cases own : owner = focal
    · subst owner
      by_cases selected : observer = focal
      · subst observer
        simp only [Function.update_self, ↓reduceIte]
      · simp only [Function.update_of_ne selected, ↓reduceIte]
    · by_cases selected : observer = focal
      · subst observer
        simp only [Function.update_self, Function.update_of_ne (Ne.symm own)]
      · simp only [Function.update_of_ne selected]
        by_cases acting : observer = owner
        · subst observer
          simp only [Function.update_self, Function.update_of_ne own, ite_eq_right own]
        · simp only [Function.update_of_ne acting, Function.update_of_ne selected]

end Vegas.SourceProgram.Config
