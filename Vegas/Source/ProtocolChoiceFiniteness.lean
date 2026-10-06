/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolBehavioral
import GameTheoryExtensions.Math.Probability.Support

/-! # Finite source choices at arbitrary decision views

Only payload types of fresh commitment instructions must be finite. Initial
types, public sample results and the ambient information carriers may remain
infinite. This suffices to complete policies at unreachable information values
using a uniform law over their existing legal choices, which are never empty.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem ProtocolView.available_finite (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → program.FiniteBindingTypes →
    (admission : CommitmentInterface program) → (view : ProtocolView who program) →
    (ProtocolView.available who program admission view).Finite
  | _, _, .ret _, _, _, _ => Set.finite_empty
  | _, _, .sample _ _ _ next, finite, admission, view => by
      cases view with
      | inl _ => exact Set.finite_empty
      | inr later => exact available_finite who next finite admission later
  | _, _, .commit (payload := payload) name owner _ _ next, finite, admission, view => by
      cases view with
      | inl _ =>
          let := finite.1
          let := Fintype.ofFinite (L.Val payload)
          apply (Set.finite_range (fun choice : PublicationResult (L.Val payload) =>
            OwnAction.commit owner name payload choice)).subset
          rintro _ ⟨choice, _, rfl⟩
          exact ⟨choice, rfl⟩
      | inr later =>
          exact available_finite who next finite.2 (fun site => admission (some site)) later
  | _, _, .reveal _ owner name _ _ _ next, finite, admission, view => by
      cases view with
      | inl _ =>
          apply (Set.finite_range (fun disclose => OwnAction.reveal owner name disclose)).subset
          rintro _ ⟨disclose, rfl⟩
          exact ⟨disclose, rfl⟩
      | inr later => exact available_finite who next finite admission later

theorem ProtocolView.finite_choice (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (finite : program.FiniteBindingTypes)
    (admission : CommitmentInterface program) (view : ProtocolView who program) :
    Finite {action : Option (OwnAction Player L) //
      ProtocolView.menu who program admission view action} := by
  apply Set.Finite.to_subtype
  have all := (ProtocolView.available_finite who program finite admission view).image some
  apply (all.insert none).subset
  intro action legal
  cases action with
  | none => exact Set.mem_insert _ _
  | some action => exact Set.mem_insert_of_mem _ ⟨action, legal.2, rfl⟩

/-- Every abstract setup information value has finite legal choices under
finite fresh-binding alphabets; reachability is not needed for this fact. -/
theorem Setup.finite_choice (setup : Setup (Player := Player) (L := L))
    (finite : setup.program.FiniteBindingTypes) (admission : CommitmentInterface setup.program)
    (who : Player) (info : setup.ProtocolView who) :
    Finite ((setup.informationModel admission).Choice who info) := by
  cases info with
  | none =>
      apply Finite.of_injective (fun _ : (setup.informationModel admission).Choice who none =>
        PUnit.unit)
      intro first second _
      apply Subtype.ext
      exact first.2.trans second.2.symm
  | some view => exact ProtocolView.finite_choice who setup.program finite admission view

/-- Every abstract view has a legal choice: none for a player not on the move,
a value binding at its own commitment and a withholding at its own reveal. -/
theorem ProtocolView.exists_menu (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : ProtocolView who program) →
      ∃ choice, ProtocolView.menu who program admission view choice
  | _, _, .ret _, _, _ => ⟨none, by simp [ProtocolView.menu, ProtocolView.actor]⟩
  | _, _, .sample _ _ _ next, admission, view => by
      cases view with
      | inl _ => exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor]⟩
      | inr later => exact exists_menu who next admission later
  | _, _, .commit (payload := payload) name owner _ _ next, admission, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · exact ⟨some (.commit owner name payload (.success (L.someValue payload))),
              by simp [ProtocolView.menu, ProtocolView.actor, ProtocolView.available, own]⟩
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own]⟩
      | inr later => exact exists_menu who next (fun site => admission (some site)) later
  | _, _, .reveal _ owner name _ _ _ next, admission, view => by
      cases view with
      | inl _ =>
          by_cases own : owner = who
          · exact ⟨some (.reveal owner name false),
              by simp [ProtocolView.menu, ProtocolView.actor, ProtocolView.available, own]⟩
          · exact ⟨none, by simp [ProtocolView.menu, ProtocolView.actor, own]⟩
      | inr later => exact exists_menu who next admission later

/-- Every abstract setup information value has a legal choice. -/
theorem Setup.choice_nonempty (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player)
    (info : setup.ProtocolView who) :
    Nonempty ((setup.informationModel admission).Choice who info) := by
  cases info with
  | none => exact ⟨⟨none, rfl⟩⟩
  | some view =>
      obtain ⟨choice, legal⟩ := ProtocolView.exists_menu who setup.program admission view
      exact ⟨⟨choice, legal⟩⟩

end Vegas.SourceProgram
