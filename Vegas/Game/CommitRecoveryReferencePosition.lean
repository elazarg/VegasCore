/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryReference
import Vegas.Game.CommitRecoveryClearDecoder
import Vegas.Source.ObservationRecall

/-! # Source reference choices depend only on their static address -/

noncomputable section

namespace Vegas.SourceProgram.ProtocolView

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Forfeiture menus retain every typed result. Their source address, rather
than the hidden environment or earlier own choices, determines all legal moves. -/
theorem recovery_controls_of_position (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolView who program),
      position who program first = position who program second →
        actor who program first = actor who program second ∧
        recoveryAvailable who program first = recoveryAvailable who program second := by
  intro Γ O program
  induction program with
  | ret => intro first second _same; exact ⟨rfl, rfl⟩
  | sample name fresh law next ih =>
      intro first second same
      cases first <;> cases second
      · exact ⟨rfl, rfl⟩
      · simp only [position, Sum.elim_inl, Sum.elim_inr] at same; omega
      · simp only [position, Sum.elim_inl, Sum.elim_inr] at same; omega
      · exact ih _ _ (Nat.add_right_cancel same)
  | commit name owner fresh guard next ih =>
      intro first second same
      cases first <;> cases second
      · exact ⟨rfl, rfl⟩
      · simp only [position, Sum.elim_inl, Sum.elim_inr] at same; omega
      · simp only [position, Sum.elim_inl, Sum.elim_inr] at same; omega
      · exact ih _ _ (Nat.add_right_cancel same)
  | reveal published owner name fresh source unresolved next ih =>
      intro first second same
      cases first <;> cases second
      · exact ⟨rfl, rfl⟩
      · simp only [position, Sum.elim_inl, Sum.elim_inr] at same; omega
      · simp only [position, Sum.elim_inl, Sum.elim_inr] at same; omega
      · exact ih _ _ (Nat.add_right_cancel same)

end Vegas.SourceProgram.ProtocolView

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Complete information and private history may differ, while the current
static source address and the owner's exclusion status fix the legal raw menu. -/
theorem commitRecovery_menu_eq_of_position (who : Player)
    (first second : setup.commitRecoveryModel.InfoState who)
    (firstView secondView : SourceProgram.ProtocolView who setup.program)
    (currentFirst : first.1.1.1 = some firstView)
    (currentSecond : second.1.1.1 = some secondView)
    (samePosition : ProtocolView.position who setup.program firstView =
      ProtocolView.position who setup.program secondView)
    (sameExcluded : who ∈ first.1.1.2.1 ↔ who ∈ second.1.1.2.1) :
    setup.commitRecoveryModel.menu who first = setup.commitRecoveryModel.menu who second := by
  obtain ⟨actors, available⟩ :=
    ProtocolView.recovery_controls_of_position who setup.program firstView secondView samePosition
  funext choice
  apply propext
  cases choice <;>
    simp only [commitRecoveryModel, commitRecoveryMenu, commitRecoveryActive,
      currentFirst, currentSecond, Option.elim_some, actors, available, sameExcluded]

/-- Uniform source trembles have the same complete raw-action law at a fixed
source address. In particular omission does not reveal a hidden value there. -/
theorem commitRecoveryReference_raw_eq_of_menu (finite : setup.program.FiniteBindingTypes)
    (who : Player) (first second : setup.commitRecoveryModel.InfoState who)
    (menus : setup.commitRecoveryModel.menu who first =
      setup.commitRecoveryModel.menu who second) :
    ((setup.commitRecoveryReference finite).strategy who first).map Subtype.val =
      ((setup.commitRecoveryReference finite).strategy who second).map Subtype.val := by
  classical
  let := setup.commitRecovery_finite_choice finite who first
  let := setup.commitRecovery_finite_choice finite who second
  let := Fintype.ofFinite (setup.commitRecoveryModel.Choice who first)
  let := Fintype.ofFinite (setup.commitRecoveryModel.Choice who second)
  let := setup.commitRecovery_choice_nonempty who first
  let := setup.commitRecovery_choice_nonempty who second
  let equivalence : setup.commitRecoveryModel.Choice who first ≃
      setup.commitRecoveryModel.Choice who second :=
    Equiv.subtypeEquivRight (fun choice => by rw [menus])
  have uniform : (PMF.uniformOfFintype _).map equivalence = PMF.uniformOfFintype _ := by
    ext choice
    obtain ⟨prior, rfl⟩ := equivalence.surjective choice
    rw [pmf_map_apply_of_injective _ equivalence.injective]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_congr equivalence]
  change (PMF.uniformOfFintype _).map Subtype.val =
    (PMF.uniformOfFintype _).map Subtype.val
  rw [← uniform, PMF.map_comp]
  rfl

/-- The actual clear decoder may select unrelated latent source histories.
Their reference omission law nevertheless agrees at the same static address. -/
theorem commitRecoveryReference_missing_eq_of_position
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (who : Player) (first second : SourceProgram.ProtocolView who setup.program)
    (samePosition : ProtocolView.position who setup.program first =
      ProtocolView.position who setup.program second) :
    ((setup.commitRecoveryReference finite).strategy who
      (setup.commitRecoveryClearInformation wellFormed who (some first))).map
        (fun choice => CommitRecoveryMove.missed choice.1) =
      ((setup.commitRecoveryReference finite).strategy who
        (setup.commitRecoveryClearInformation wellFormed who (some second))).map
          (fun choice => CommitRecoveryMove.missed choice.1) := by
  have menus := setup.commitRecovery_menu_eq_of_position who _ _ first second
    (setup.commitRecoveryClearInformation_current wellFormed who (some first))
    (setup.commitRecoveryClearInformation_current wellFormed who (some second)) samePosition
    (by simp only [setup.commitRecoveryClearInformation_excluded])
  have raw := setup.commitRecoveryReference_raw_eq_of_menu finite who _ _ menus
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (fun law => law.map CommitRecoveryMove.missed) raw

end Vegas.SourceProgram.Setup
