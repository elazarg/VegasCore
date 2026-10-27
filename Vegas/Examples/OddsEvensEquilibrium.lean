/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensSetup
import GameTheory.Analysis.Protocol.SequentialExistence

/-! # Sequential-equilibrium existence for the intended Odds–Evens game -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

private theorem false_mem_intended {Γ : SourceCtx Player simpleExpr}
    (who owner : Player) (name : VarId) (view : SourceObservation simpleExpr who Γ) :
    false ∈ intendedValues who (acceptGuard owner name) view := by
  apply Or.inl
  intro same
  cases same
  unfold SourceGuard.predicts
  refine (GuardCode.accepts_success (acceptGuard who name).toGuardCode false _
    (fun _ _ cell _ => by
    cases cell with
    | here => exact false
    | there absent => cases absent) ?_ ?_).trans ?_
  · intro _; rfl
  · intro _ _ cell _; cases cell
  · rfl

def intendedFallbackAction (who : Player) (view : setup.ProtocolView who) :
    Option (OwnAction Player simpleExpr) :=
  match view with
  | none => none
  | some (.inl _) => if who = even then some (.commit even 0 .bool (.success false)) else none
  | some (.inr (.inl _)) => if who = odd then some (.commit odd 1 .bool (.success false)) else none
  | some (.inr (.inr (.inl _))) => if who = even then some (.reveal even 0 true) else none
  | some (.inr (.inr (.inr (.inl _)))) => if who = odd then some (.reveal odd 1 true) else none
  | some (.inr (.inr (.inr (.inr _)))) => none

theorem intendedFallbackAction_mem (who : Player) (view : setup.ProtocolView who) :
    intendedFallbackAction who view ∈ setup.intendedMenu who view := by
  cases who <;> rcases view with _ | (view | (view | (view | (view | view))))
  all_goals
    first
    | solve | simp [intendedFallbackAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd]
    | simpa [intendedFallbackAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd] using (false_mem_intended false false 0 view.1)
    | simpa [intendedFallbackAction, Setup.intendedMenu, setup, program,
        ProtocolView.intendedMenu, ProtocolView.actor, ProtocolView.intendedAvailable,
        even, odd] using (false_mem_intended true true 1 view.1)

def intendedFallback (who : Player) : setup.intendedModel.Policy who :=
  fun view => ⟨intendedFallbackAction who view, intendedFallbackAction_mem who view⟩

/-- Finite-game existence for the actual intended source game. This statement
does not identify the assessment with the particular uniform-bit strategy. -/
theorem intended_equilibrium_exists :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium setup.intended_decision_antichain
        setup.intended_bounded.wellFoundedHistories
        (fun who final => (setup.protocolReadout final.state).elim 0
          (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who)) := by
  obtain ⟨assessment, rational, consistent⟩ :=
    setup.intendedModel.exists_sequentialEquilibrium setup.intendedModel_decisionRecall
      intendedFallback
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who))
      setup.intended_bounded.wellFoundedHistories
  exact ⟨assessment, rational, consistent⟩

end Vegas.Examples.OddsEvens
