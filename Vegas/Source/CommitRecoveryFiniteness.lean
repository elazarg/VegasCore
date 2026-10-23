/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryClear
import Vegas.Source.ProtocolChoiceFiniteness

/-! # Finite menus and finite transition laws of source recovery -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem ProtocolView.recoveryAvailable_finite (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (finite : program.FiniteBindingTypes) (view : ProtocolView who program) :
    (recoveryAvailable who program view).Finite := by
  have choices := available_finite who program finite (CommitmentInterface.forfeiture program) view
  let := choices.to_subtype
  apply (Set.finite_range (fun pair :
    {action // action ∈ available who program (CommitmentInterface.forfeiture program) view} ×
      Bool =>
      (⟨pair.1.1, pair.2⟩ : CommitRecoveryMove Player L))).subset
  intro move offered
  exact ⟨(⟨move.action, offered.1⟩, move.missing), rfl⟩

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

theorem commitRecovery_finite_choice (finite : setup.program.FiniteBindingTypes) (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    Finite (setup.commitRecoveryModel.Choice who information) := by
  let moves : Set (CommitRecoveryMove Player L) := information.1.1.1.elim ∅
    (ProtocolView.recoveryAvailable who setup.program)
  have finitelyMany : moves.Finite := by
    cases current : information.1.1.1 with
    | none => simp only [moves, current, Option.elim_none]; exact Set.finite_empty
    | some view =>
        simpa only [moves, current, Option.elim_some] using
          ProtocolView.recoveryAvailable_finite who setup.program finite view
  apply Set.Finite.to_subtype
  apply ((finitelyMany.image some).insert none).subset
  intro choice legal
  cases choice with
  | none => exact Set.mem_insert _ _
  | some move =>
      apply Set.mem_insert_of_mem
      refine ⟨move, ?_, rfl⟩
      have offered := legal.2
      cases current : information.1.1.1 with
      | none => simp only [current, Option.elim_none] at offered
      | some view => simpa only [moves, current, Option.elim_some] using offered

theorem commitRecovery_choice_nonempty (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    Nonempty (setup.commitRecoveryModel.Choice who information) := by
  classical
  by_cases active : setup.commitRecoveryActive who information.1.1
  · cases current : information.1.1.1 with
    | none => simp only [commitRecoveryActive, current, Option.elim_none] at active
    | some view =>
        have acting := active
        simp only [commitRecoveryActive, current, Option.elim_some] at acting
        have actor := acting.1
        obtain ⟨choice, legal⟩ := ProtocolView.exists_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) view
        cases choice with
        | none => exact (legal actor).elim
        | some action =>
            refine ⟨⟨some ⟨action, false⟩, active, ?_⟩⟩
            simp only [current, Option.elim_some]
            refine ⟨legal.2, ?_⟩
            dsimp only
            split
            · intro impossible; cases impossible
            · rfl
  · exact ⟨⟨none, active⟩⟩

end Setup

namespace ProtocolState

theorem recoveryStep_support_finite : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L)),
    (recoveryStep program point excluded joint).support.Finite
  | _, _, .ret _, _, _, _ => by
      simp only [recoveryStep, PMF.support_pure]
      exact Set.finite_singleton _
  | _, _, .sample _ _ _ next, point, excluded, joint => by
      cases point with
      | inl _ =>
          rw [recoveryStep, Sum.elim_inl, PMF.support_map]
          exact (L.evalDist_support_finite _ _).image _
      | inr later =>
          rw [recoveryStep, Sum.elim_inr, PMF.support_map]
          exact (recoveryStep_support_finite next later excluded joint).image _
  | _, _, .commit _ _ _ _ next, point, excluded, joint => by
      cases point with
      | inl _ =>
          simp only [recoveryStep, Sum.elim_inl]
          split <;> rw [PMF.support_pure] <;> exact Set.finite_singleton _
      | inr later =>
          rw [recoveryStep, Sum.elim_inr, PMF.support_map]
          exact (recoveryStep_support_finite next later excluded joint).image _
  | _, _, .reveal _ _ _ _ _ _ next, point, excluded, joint => by
      cases point with
      | inl _ =>
          simp only [recoveryStep, Sum.elim_inl, PMF.support_pure]
          exact Set.finite_singleton _
      | inr later =>
          rw [recoveryStep, Sum.elim_inr, PMF.support_map]
          exact (recoveryStep_support_finite next later excluded joint).image _

end ProtocolState

theorem CommitRecoveryState.step_support_finite
    {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
    (state : CommitRecoveryState program) (joint : Player → Option (CommitRecoveryMove Player L)) :
    (state.step joint).support.Finite := by
  let raw := ProtocolState.recoveryStep program state.point state.excluded joint
  have finite := ProtocolState.recoveryStep_support_finite program state.point state.excluded joint
  unfold CommitRecoveryState.step
  rw [PMF.support_map]
  apply Set.Finite.image
  let keep := fun result supported => ProtocolState.recoveryStep_excluded_monotone
    program state.point state.excluded joint result supported
  have projects := map_val_pmfToSubtype raw keep
  have injective : Function.Injective (Subtype.val : {result // state.excluded ⊆ result.2} →
      ProtocolState program × Finset Player) := Subtype.val_injective
  have imageFinite := finite
  change raw.support.Finite at imageFinite
  rw [← projects, PMF.support_map] at imageFinite
  exact imageFinite.of_finite_image injective.injOn

namespace Setup

theorem commitRecovery_step_support_finite (setup : Setup (Player := Player) (L := L))
    [setup.FiniteInitialLaw] (state : setup.commitRecoveryProtocol.State)
    (draw : {joint // setup.commitRecoveryProtocol.Legal state joint}) :
    (setup.commitRecoveryProtocol.step state draw).support.Finite := by
  cases state with
  | none =>
      change (setup.initialLaw.map _).support.Finite
      rw [PMF.support_map]
      exact setup.initialLaw_support_finite.image _
  | some current =>
      change ((current.step draw.1).map some).support.Finite
      rw [PMF.support_map]
      exact (current.step_support_finite draw.1).image _

end Setup
end Vegas.SourceProgram
