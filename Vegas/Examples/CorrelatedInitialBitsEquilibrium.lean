module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.CorrelatedInitialBitsService
public import Vegas.Game.ObservedComponentEquilibrium
public import GameTheory.Analysis.Protocol.SequentialExistence

@[expose] public section

/-! # Equilibrium existence in the privately correlated Odds–Evens game -/

noncomputable section

namespace Vegas.Examples.CorrelatedInitialBits.Service

open SourceProgram

private theorem intendedMenu_nonempty (who : Player) : ∀ {ctx : SourceCtx Player simpleExpr}
    {owed : Finset VarId} (game : SourceProgram Player simpleExpr ctx owed)
    (view : ProtocolView who game), ∃ choice, ProtocolView.intendedMenu who game view choice
  | _, _, .ret _, _ => ⟨none, by simp [ProtocolView.intendedMenu, ProtocolView.actor]⟩
  | _, _, .sample _ _ _ next, view => by
    cases view with
    | inl _ => exact ⟨none, by simp [ProtocolView.intendedMenu, ProtocolView.actor]⟩
    | inr later => exact intendedMenu_nonempty who next later
  | _, _, .commit name owner _ guard next, current => by
    cases current with
    | inr later => exact intendedMenu_nonempty who next later
    | inl view =>
      by_cases active : (if owner ∈ view.defaulted then none else some owner) = some who
      · obtain ⟨value, member⟩ := intendedValues_nonempty who guard view.observation
        exact ⟨some (.commit owner name _ (some (.success value))), active, value, member, rfl⟩
      · exact ⟨none, active⟩
  | _, _, .reveal _ owner name _ _ _ next, current => by
    cases current with
    | inr later => exact intendedMenu_nonempty who next later
    | inl view =>
      by_cases active : (if owner ∈ view.defaulted then none else some owner) = some who
      · exact ⟨some (.reveal owner name true), active, rfl⟩
      · exact ⟨none, active⟩

/-- At least one intended sequential equilibrium of the concrete game exists. -/
theorem intended_equilibrium_exists :
    ∃ assessment, setup.IntendedSequentialEquilibrium (fun _ => ()) utility assessment := by
  let fallback (who : Player) : setup.intendedModel.Policy who := fun view => by
    cases view with
    | none => exact ⟨none, rfl⟩
    | some view =>
      exact ⟨(intendedMenu_nonempty who program view).choose,
        (intendedMenu_nonempty who program view).choose_spec⟩
  exact setup.intendedModel.exists_sequentialEquilibrium setup.intendedModel_decisionRecall
    fallback _ setup.intended_bounded.wellFoundedHistories

local notation "raw" => bounds.rawMenu timeouts leaks
local notation "initial" => Vegas.initialDistribution setup
local notation "ledger" => Interaction.ReactiveApplication.ResponseMenu.information (raw)
  initial horizon scheduler

/-- Every intended sequential equilibrium of the correlated-bit game is realized by
a sequential equilibrium of the periodic raw ledger game on the original correlated prior. -/
theorem sequentialEquilibrium_preserved (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium (fun _ => ()) utility intended) :
    ∃ A : (ledger).BehavioralAssessment,
      A.IsSequentialEquilibrium ((raw).decisionInformationAntichain initial horizon scheduler)
        ((raw).bounded initial horizon scheduler).wellFoundedHistories
        (fun who h => (specification false).payoff who h.state) ∧
      (((raw).run initial horizon scheduler A.strategy).bind fun h =>
        (specification false).observation h.state) =
        (setup.intendedModel.runBehavioral intended.strategy (instructionCount program + 1)).map
          (intendedReadoutExclusion setup (fun _ => ()) utility (fun _ => 0)) := by
  exact ⟨_, Setup.compileComponent_sequentialEquilibrium (setup := setup) (timeouts := timeouts)
    (leaks := leaks) (bounds := bounds) (horizon := horizon) (scheduler := scheduler)
    (parameter := fun _ => ()) (utility := utility) (exit := fun _ => 0) signal signal_supported
    informationFiber_component specification intended equilibrium false ledgerBit ledgerBit_observe
    wellFormed (fun _ => rfl) (fun _ => rfl)⟩

end Vegas.Examples.CorrelatedInitialBits.Service
