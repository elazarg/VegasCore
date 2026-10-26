/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.FailureContinuationScope
import Vegas.Game.SourcePhaseGame

/-! # Actual permanent source exit after withholding

The source phase kernel executes the same program used to distinguish the
continuing source interface. An actual legal initialized withholding prefix
excludes its owner. Declared cash of minus one then applies and the later
information value admits only silence. A separately declared valuation of seven
is retained, giving utility six; cash settlement does not clip valuation.
-/

noncomputable section

namespace Vegas.Examples.FailureContinuationScope

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

private def phaseEntry : CommitRecoveryState program :=
  .atPoint (ProtocolState.entry program (setup.initialConfig initial)) ∅ 0

private def withholdingMove : CommitRecoveryMove Player simpleExpr :=
  ⟨.reveal owner 0 false, false⟩

private theorem phase_draw_legal : setup.commitRecoveryProtocol.Legal none (fun _ => none) :=
  ⟨fun impossible => impossible, fun _ impossible => impossible⟩

private theorem phase_draw_supported : some phaseEntry ∈
    (setup.commitRecoveryProtocol.step none ⟨fun _ => none, phase_draw_legal⟩).support := by
  change some phaseEntry ∈ ((PMF.pure initial).map _).support
  simp only [PMF.pure_map, PMF.mem_support_pure_iff]
  rfl

private def phaseDraw : setup.commitRecoveryProtocol.Trace (some phaseEntry) :=
  .extend .start (fun _ => none) phase_draw_legal phase_draw_supported

private theorem phase_withholding_legal : setup.commitRecoveryProtocol.Legal (some phaseEntry)
    (fun _ => some withholdingMove) := by
  refine ⟨fun impossible => impossible, ?_⟩
  intro who
  refine ⟨⟨by cases who; rfl, Finset.notMem_empty _⟩, ?_⟩
  exact ⟨⟨false, rfl⟩, rfl⟩

private theorem withholding_excludes (next : CommitRecoveryState program)
    (supported : next ∈ (phaseEntry.step (fun _ => some withholdingMove)).support) :
    owner ∈ next.excluded := by
  obtain ⟨result, raw, reached⟩ := phaseEntry.step_raw_result _ next supported
  have law : ProtocolState.recoveryStep program phaseEntry.point phaseEntry.excluded
      (fun _ => some withholdingMove) =
        PMF.pure ((ProtocolState.entry continuation
          (revealSuccessor 1 (.here : HasVar context 0 (.commitment owner .bool))
            (setup.initialConfig initial) false) |> Sum.inr), {owner}) := rfl
  rw [law] at raw
  have same := (PMF.mem_support_pure_iff _ _).mp raw
  rw [reached, CommitRecoveryState.close_excluded]
  change owner ∈ result.1.2
  rw [same]
  exact Finset.mem_singleton_self _

/-- The existing initialized phase executor reaches actual exclusion. At that
information value every legal local choice is silence, while independent
history valuation is retained alongside the declared exit cash. -/
theorem source_phase_withholding_exit :
    ∃ history : setup.commitRecoveryProtocol.History,
      (∃ current, history.state = some current ∧ owner ∈ current.excluded) ∧
      setup.sourcePhaseCash history owner = -1 ∧
      (setup.sourcePhaseGame (fun _ _ => 7)).utility history owner = 6 ∧
      ∀ choice : setup.commitRecoveryModel.Choice owner
        (setup.commitRecoveryModel.infoOf owner history.trace), choice.1 = none := by
  obtain ⟨next, supported⟩ := (phaseEntry.step (fun _ => some withholdingMove)).support_nonempty
  have excluded := withholding_excludes next supported
  have moved : some next ∈ (setup.commitRecoveryProtocol.step (some phaseEntry)
      ⟨fun _ => some withholdingMove, phase_withholding_legal⟩).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨next, supported, rfl⟩
  let history : setup.commitRecoveryProtocol.History :=
    ⟨some next, .extend phaseDraw (fun _ => some withholdingMove) phase_withholding_legal moved⟩
  refine ⟨history, ⟨next, rfl, excluded⟩, ?_, ?_, ?_⟩
  · exact setup.sourcePhaseCash_of_excluded history next rfl owner excluded
  · rw [setup.sourcePhaseGame_utility_of_excluded _ history next rfl owner excluded]
    change (7 : ℝ) + (-1 : Int) = 6
    norm_num
  · exact setup.sourcePhase_choice_eq_none_of_excluded history next rfl owner excluded

end Vegas.Examples.FailureContinuationScope
