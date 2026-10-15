/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.FailedGuardRegistry
import Vegas.Source.FailureRevelations

/-! # Compiler guard registries may retain inert failed subjects -/

namespace Vegas.SourceProgram.Registry

variable {Player : Type} {L : IExpr} {Γ : SourceCtx Player L}

/-- The larger registry adds only obligations whose immutable bindings failed. -/
structure FailureExtension (smaller larger : Registry (Player := Player) (L := L) Γ)
    (state : State L Γ) : Prop where
  included : smaller ⊆ larger
  extra : ∀ obligation ∈ larger,
    obligation ∈ smaller ∨ state.get obligation.source = .failure

namespace FailureExtension

theorem refl (registry : Registry (Player := Player) (L := L) Γ) (state : State L Γ) :
    FailureExtension registry registry state :=
  ⟨fun _ member => member, fun _ member => Or.inl member⟩

/-- Extending the source context preserves all old failed binding meanings. -/
theorem weaken {smaller larger : Registry (Player := Player) (L := L) Γ} {state : State L Γ}
    (valid : FailureExtension smaller larger state) {name : VarId} {cell : CellTy Player L}
    (head : CellVal L cell) :
    FailureExtension (smaller.weaken (x := name) (c := cell))
      (larger.weaken (x := name) (c := cell))
      (Env.cons head state) := by
  constructor
  · intro obligation member
    obtain ⟨before, prior, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨before, valid.included prior, rfl⟩
  · intro obligation member
    obtain ⟨before, prior, rfl⟩ := List.mem_map.mp member
    rcases valid.extra before prior with common | failed
    · exact Or.inl (List.mem_map.mpr ⟨before, common, rfl⟩)
    · exact Or.inr failed

/-- An active source commitment installs the same obligation on both sides. -/
theorem cons {smaller larger : Registry (Player := Player) (L := L) Γ} {state : State L Γ}
    (valid : FailureExtension smaller larger state) (obligation : Obligation Γ) :
    FailureExtension (obligation :: smaller) (obligation :: larger) state := by
  constructor
  · intro query member
    rcases List.mem_cons.mp member with same | previous
    · exact List.mem_cons.mpr (Or.inl same)
    · exact List.mem_cons.mpr (Or.inr (valid.included previous))
  · intro query member
    rcases List.mem_cons.mp member with same | previous
    · exact Or.inl (List.mem_cons.mpr (Or.inl same))
    · rcases valid.extra query previous with common | failed
      · exact Or.inl (List.mem_cons.mpr (Or.inr common))
      · exact Or.inr failed

/-- An automatic failed slot adds a compiler obligation while source execution
records no voluntary guard obligation for that excluded slot. -/
theorem failed_cons {smaller larger : Registry (Player := Player) (L := L) Γ}
    {state : State L Γ} (valid : FailureExtension smaller larger state)
    (obligation : Obligation Γ) (failed : state.get obligation.source = .failure) :
    FailureExtension smaller (obligation :: larger) state := by
  constructor
  · intro query member
    exact List.mem_cons.mpr (Or.inr (valid.included member))
  · intro query member
    rcases List.mem_cons.mp member with same | previous
    · subst query
      exact Or.inr failed
    · exact valid.extra query previous

/-- Retaining automatic failed subjects changes no source reveal decision.
The actual proposal preserves failed bindings before either registry is checked. -/
theorem completedBy_all_eq {smaller larger : Registry (Player := Player) (L := L) Γ}
    {state : State L Γ} (valid : FailureExtension smaller larger state)
    (revelations : Revelations Γ) (failures : Revelations.PreservesFailures revelations state)
    (unique : (Γ.map Prod.fst).Nodup)
    {name published : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload)) (disclose : Bool) :
    let nextRevelations : Revelations ((published, .publication payload) :: Γ) :=
      revelations.reveal (published := published) source
    let proposal : PublicationResult (L.Val payload) :=
      if disclose then state.get source else .failure
    let nextState := Env.cons (Val := CellVal (Player := Player) L) (x := published)
      (τ := .publication payload) proposal state
    (smaller.completedBy (published := published) revelations source).all
        (·.accepts nextRevelations nextState) =
      (larger.completedBy (published := published) revelations source).all
        (·.accepts nextRevelations nextState) := by
  dsimp only
  let proposal : PublicationResult (L.Val payload) :=
    if disclose then state.get source else .failure
  let proposed := Env.cons (Val := CellVal (Player := Player) L) (x := published)
    (τ := .publication payload) proposal state
  let revealed : Revelations ((published, .publication payload) :: Γ) :=
    revelations.reveal (published := published) source
  have preserved : Revelations.PreservesFailures revealed proposed :=
    failures.reveal (published := published) unique source
      (if disclose then state.get source else .failure) (fun failed => by
        cases disclose with
        | false => rfl
        | true => exact failed)
  have iffTrue :
      (smaller.completedBy (published := published) revelations source).all
          (·.accepts revealed proposed) = true ↔
        (larger.completedBy (published := published) revelations source).all
          (·.accepts revealed proposed) = true := by
    rw [List.all_eq_true, List.all_eq_true]
    constructor
    · intro accepted obligation member
      obtain ⟨before, filtered, rfl⟩ := List.mem_map.mp member
      obtain ⟨oldMember, completed⟩ := List.mem_filter.mp filtered
      rcases valid.extra before oldMember with common | failed
      · exact accepted before.weaken (List.mem_map.mpr
          ⟨before, List.mem_filter.mpr ⟨common, completed⟩, rfl⟩)
      · exact before.weaken.accepts_of_subject_failure revealed proposed
          (preserved before.owner before.payload before.subject (.there before.source) failed)
    · intro accepted obligation member
      obtain ⟨before, filtered, rfl⟩ := List.mem_map.mp member
      obtain ⟨oldMember, completed⟩ := List.mem_filter.mp filtered
      exact accepted before.weaken (List.mem_map.mpr
        ⟨before, List.mem_filter.mpr ⟨valid.included oldMember, completed⟩, rfl⟩)
  cases smallerResult : (smaller.completedBy (published := published) revelations source).all
      (·.accepts revealed proposed) <;>
    cases largerResult : (larger.completedBy (published := published) revelations source).all
      (·.accepts revealed proposed) <;> simp_all

end FailureExtension

end Vegas.SourceProgram.Registry
