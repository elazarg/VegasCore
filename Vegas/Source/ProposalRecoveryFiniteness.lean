/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryInformation
import Vegas.Source.CommitRecoveryFiniteness
import GameTheoryExtensions.Analysis.Protocol.Bayes
import Mathlib.Probability.Distributions.Uniform

/-! # Finite histories of proposal-labeled recovery without global value finiteness -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

theorem proposalRecovery_finite_choice (finite : setup.program.FiniteBindingTypes) (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    Finite (setup.proposalRecoveryModel.Choice who information) := by
  let moves : Set (CommitRecoveryMove Player L) := information.1.1.1.elim ∅
    (ProtocolView.recoveryAvailable who setup.program)
  have finitelyMany : moves.Finite := by
    cases current : information.1.1.1 with
    | none => simp only [moves, current, Option.elim_none]; exact Set.finite_empty
    | some view =>
        simpa only [moves, current, Option.elim_some] using
          ProtocolView.recoveryAvailable_finite who setup.program finite view
  let := finitelyMany.to_subtype
  have labels := Set.finite_range (fun pair : {move // move ∈ moves} × Bool =>
    some (ProposalRecoveryMove.mk pair.1.1 pair.2))
  apply Set.Finite.to_subtype
  apply (labels.insert none).subset
  intro choice legal
  cases choice with
  | none => exact Set.mem_insert _ _
  | some move =>
      apply Set.mem_insert_of_mem
      refine ⟨(⟨move.semantic, ?_⟩, move.proposed), ?_⟩
      · have offered := legal.2
        cases current : information.1.1.1 with
        | none => simp only [current, Option.elim_none] at offered
        | some view =>
            have offered' : move.semantic ∈
                ProtocolView.recoveryAvailable who setup.program view ∧ move.Valid := by
              simpa only [current, Option.elim_some] using offered
            simpa only [moves, current, Option.elim_some] using offered'.1
      · cases move; rfl

theorem proposalRecovery_choice_nonempty (who : Player)
    (information : setup.proposalRecoveryModel.InfoState who) :
    Nonempty (setup.proposalRecoveryModel.Choice who information) := by
  classical
  by_cases active : setup.proposalRecoveryActive who information.1.1
  · cases current : information.1.1.1 with
    | none => simp only [proposalRecoveryActive, commitRecoveryActive, current,
        Option.elim_none] at active
    | some view =>
        have acting := active
        simp only [proposalRecoveryActive, commitRecoveryActive, current,
          Option.elim_some] at acting
        obtain ⟨choice, legal⟩ := ProtocolView.exists_menu who setup.program
          (CommitmentInterface.forfeiture setup.program) view
        cases choice with
        | none => exact (legal acting.1).elim
        | some action =>
            refine ⟨⟨some (ProposalRecoveryMove.ordinary ⟨action, false⟩), active, ?_⟩⟩
            simp only [current, Option.elim_some]
            refine ⟨⟨legal.2, ?_⟩, ProposalRecoveryMove.ordinary_valid _⟩
            split
            · intro impossible; cases impossible
            · rfl
  · exact ⟨⟨none, active⟩⟩

def proposalRecoveryReference (finite : setup.program.FiniteBindingTypes) :
    setup.proposalRecoveryModel.BehavioralAssessment :=
  .ofStrategy fun who information =>
    let := setup.proposalRecovery_finite_choice finite who information
    let := Fintype.ofFinite (setup.proposalRecoveryModel.Choice who information)
    let := setup.proposalRecovery_choice_nonempty who information
    PMF.uniformOfFintype _

theorem proposalRecoveryReference_fullyMixed (finite : setup.program.FiniteBindingTypes) :
    (setup.proposalRecoveryReference finite).IsFullyMixed := by
  intro who site choice
  let := setup.proposalRecovery_finite_choice finite who site.1
  let := Fintype.ofFinite (setup.proposalRecoveryModel.Choice who site.1)
  let := setup.proposalRecovery_choice_nonempty who site.1
  exact PMF.mem_support_uniformOfFintype choice

theorem proposalRecovery_step_support_finite [setup.FiniteInitialLaw]
    (state : setup.proposalRecoveryProtocol.State)
    (joint : {joint // setup.proposalRecoveryProtocol.Legal state joint}) :
    (setup.proposalRecoveryProtocol.step state joint).support.Finite :=
  setup.commitRecovery_step_support_finite state
    ⟨proposalRecoveryJoint joint.1, setup.proposalRecovery_erase_legal joint.1 joint.2⟩

theorem proposalRecovery_finite_history [Finite Player]
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] :
    Finite setup.proposalRecoveryProtocol.History := by
  let := Fintype.ofFinite Player
  exact (setup.proposalRecoveryReference_fullyMixed finite).finite_history
    setup.proposalRecoveryProtocol_bounded
    (fun who information =>
      have := setup.proposalRecovery_finite_choice finite who information
      Set.toFinite _)
    (fun {state} joint => setup.proposalRecovery_step_support_finite state joint)

end Vegas.SourceProgram.Setup
