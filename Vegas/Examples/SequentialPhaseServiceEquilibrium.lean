/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.SequentialPhaseService
import GameTheory.Analysis.Protocol.SequentialExistence
import Vegas.Game.SequentialPhaseRawPreservation
import Vegas.Pending.PhaseCountCollection

/-! # A funded raw equilibrium for private Boolean publication

The finite intended source has a sequential equilibrium. Its executable
conditional payment, complete authentic audit, deposit of three and proved
physical service instantiate the raw phase preservation theorem.
-/

noncomputable section

namespace Vegas.Examples.SequentialPhaseService

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement

def sourceUtility (result : Unit × PublicOutcome program) (_who : Player) : ℝ :=
  if (result.2.get .here : PublicationResult Bool).getD false then 2 else 0

theorem sourceUtility_bounds (result : Unit × PublicOutcome program) (who : Player) :
    0 ≤ sourceUtility result who ∧ sourceUtility result who ≤ 2 := by
  unfold sourceUtility
  split <;> norm_num

theorem sourceUtility_eq_programTransfer (result : Unit × PublicOutcome program) (who : Player) :
    sourceUtility result who = program.publicTransfers result.2 who := by
  have payments : program.publicPayoffs result.2 =
      [(owner, if (result.2.get .here : PublicationResult Bool).getD false then 2 else 0)] := rfl
  unfold SourceProgram.publicTransfers
  rw [payments]
  unfold sourceUtility
  cases who
  split <;> norm_num [transferAmount]

def intendedFallbackAction (who : Player) (view : setup.ProtocolView who) :
    Option (OwnAction Player simpleExpr) :=
  match view with
  | none => none
  | some (.inl _) => some (.reveal owner 0 true)
  | some (.inr _) => none

theorem intendedFallbackAction_mem (who : Player) (view : setup.ProtocolView who) :
    intendedFallbackAction who view ∈ setup.intendedMenu who view := by
  cases who
  cases view with
  | none => rfl
  | some view =>
    cases view with
    | inl observed =>
      change some owner = some owner ∧ OwnAction.reveal owner 0 true ∈
        ({OwnAction.reveal owner 0 true} : Set (OwnAction Player simpleExpr))
      exact ⟨rfl, rfl⟩
    | inr observed =>
      change none ≠ some owner
      simp

def intendedFallback (who : Player) : setup.intendedModel.Policy who :=
  fun view => ⟨intendedFallbackAction who view, intendedFallbackAction_mem who view⟩

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

theorem funded_raw_equilibrium_exists :
    let initial := SequentialPhase.phaseInitialLaw setup
    let raw := PhaseCount.rawMenu runtime leaks bounds
    let observe := app.stateTraffic
    let audit := PhaseCount.audit runtime leaks
      (EvidenceReportService.complete (PhaseCount.Evidence compiled)).sample
    let base := phaseExclusionBase setup .sequential runtime leaks
      (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal)) (fun _ => -1)
    let payoff := TerminalAudit.utility base observe audit (fun _ => 3)
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial horizon scheduler)
        (raw.bounded initial horizon scheduler).wellFoundedHistories
        (fun who final => payoff final.state who) := by
  intro initial raw observe audit base payoff
  let : app.FiniteNature (SequentialPhase.phaseInitialLaw setup) scheduler :=
    (inferInstance : app.FiniteNature Vegas.Examples.SequentialPhaseService.initial scheduler)
  obtain ⟨intended, equilibrium⟩ := intended_equilibrium_exists
  obtain ⟨target, rational, _⟩ :=
    SequentialPhase.intended_raw_sequentialEquilibrium_preserved setup leaks bounds horizon
      scheduler (fun _ => ()) sourceUtility (fun _ => -1)
      wellFormed independent observable opportunity protectedInclusion completesPlay timely
      (fun _ => 0) (fun _ => 2)
      (fun result who => (sourceUtility_bounds result who).1)
      (fun result who => (sourceUtility_bounds result who).2)
      (fun final terminal _ who => le_trans (by norm_num)
        (sourceUtility_bounds (setup.parameterOutcome (fun _ => ()) terminal) who).1)
      intended equilibrium outputValues inputValues candidateCapacity
      (EvidenceReportService.complete (PhaseCount.Evidence compiled))
      (fun _ => 1) (fun _ => 1) (fun _ => by norm_num) PhaseCount.completeEvidence_coverage
      (fun _ => 3) (fun _ => by norm_num) (fun _ => by norm_num)
  refine ⟨target, ?_⟩
  exact (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _ _
    (raw.bounded initial horizon scheduler) _).mpr rational

end Vegas.Examples.SequentialPhaseService
