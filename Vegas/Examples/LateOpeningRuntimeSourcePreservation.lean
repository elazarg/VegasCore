/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.LateOpeningRuntimeSource
import Vegas.Game.IntendedPreservation
import Vegas.Game.ExclusionExtension

/-! # Preservation when the source allows withholding

This is the actual initialized three-instruction source game. Binding admission
allows only values, while either publication can fail. A forfeit covering both
players' gross payoff ranges extends every intended sequential equilibrium,
with its joint terminal-store and payoff law intact. This is a source result;
it introduces no scheduler or assumptions about pending network packets.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory.Protocol

abbrev withholdingProtocol :=
  setup.executionProtocol (CommitmentInterface.values setup.program)

abbrev withholdingModel :=
  setup.informationModel (CommitmentInterface.values setup.program)

theorem withholding_bounded : withholdingProtocol.BoundedHorizon 4 :=
  setup.protocol_bounded _

def withholdingPayoff (reward forfeit : ℝ) (who : Player)
    (history : withholdingProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal =>
    forfeitUtility setup.program forfeit (grossUtility reward)
      (setup.parameterOutcome parameter terminal) who)

def intendedTerminalLaw (reward : ℝ)
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :=
  (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile setup.intendedProtocol.initHistory).map
    (fun final => (setup.protocolReadout final.state, fun who => intendedPayoff reward who final))

def withholdingTerminalLaw (reward forfeit : ℝ)
    (profile : ∀ who, withholdingModel.BehavioralPolicy who) :=
  (withholdingModel.runBehavioralTerminalFrom
      withholding_bounded.wellFoundedHistories profile withholdingProtocol.initHistory).map
    (fun final => (setup.protocolReadout final.state,
      fun who => withholdingPayoff reward forfeit who final))

theorem grossUtility_range {reward forfeit : ℝ} (nonnegative : 0 ≤ reward)
    (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit) :
    ∀ high low who, grossUtility reward high who - grossUtility reward low who ≤ forfeit := by
  intro high low who
  fin_cases who
  · have higher := alice_gross_bounds nonnegative high
    have lower := alice_gross_bounds nonnegative low
    change grossUtility reward high alice - grossUtility reward low alice ≤ forfeit
    linarith
  · have higher := bob_gross_bounds reward high
    have lower := bob_gross_bounds reward low
    change grossUtility reward high bob - grossUtility reward low bob ≤ forfeit
    linarith

/-- Every intended assessment extends to the source game with optional failed
publications. The extension has no failed publication on its equilibrium path. -/
theorem intended_equilibrium_preserved_under_withholding {reward forfeit : ℝ}
    (nonnegative : 0 ≤ reward) (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
      setup.intended_bounded.wellFoundedHistories (intendedPayoff reward)) :
    ∃ target : withholdingModel.BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _)
        withholding_bounded.wellFoundedHistories (withholdingPayoff reward forfeit) ∧
      (∀ final ∈ (withholdingModel.runBehavioralTerminalFrom
          withholding_bounded.wellFoundedHistories target.strategy
          withholdingProtocol.initHistory).support,
        ∀ terminal, setup.protocolReadout final.state = some terminal →
          ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      withholdingTerminalLaw reward forfeit target.strategy =
        intendedTerminalLaw reward intended.strategy := by
  exact setup.intended_sequentialEquilibrium_preserved
      (CommitmentInterface.values setup.program) finiteBindingTypes wellFormed parameter
    (grossUtility reward) forfeit (grossUtility_range nonnegative coversAlice coversBob)
    setup.intended_bounded.wellFoundedHistories withholding_bounded.wellFoundedHistories
    intended equilibrium

def exclusionPayoff (reward excluded : ℝ) (who : Player)
    (history : setup.exclusionProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal =>
    exclusionUtility setup.program (fun _ => excluded) (grossUtility reward)
      (setup.parameterOutcome parameter terminal) who)

def exclusionTerminalLaw (reward excluded : ℝ)
    (profile : ∀ who, setup.exclusionModel.BehavioralPolicy who) :=
  (setup.exclusionModel.runBehavioralTerminalFrom
      setup.exclusion_bounded.wellFoundedHistories profile setup.exclusionProtocol.initHistory).map
    (fun final => (setup.protocolReadout final.state,
      fun who => exclusionPayoff reward excluded who final))

/-- Every intended assessment also extends to the source game in which a player
whose publication fails is excluded with a fixed payoff at most zero. The
extension keeps the intended strategies and the joint terminal law. -/
theorem intended_equilibrium_extends_to_exclusion {reward excluded : ℝ}
    (nonnegative : 0 ≤ reward) (low : excluded ≤ 0)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
      setup.intended_bounded.wellFoundedHistories (intendedPayoff reward)) :
    ∃ target : setup.exclusionModel.BehavioralAssessment,
      target.IsSequentialEquilibrium setup.exclusion_decisionRecall.decisionInformationAntichain
        setup.exclusion_bounded.wellFoundedHistories (exclusionPayoff reward excluded) ∧
      (setup.exclusionRestriction wellFormed).ExtendsProfile intended.strategy
        target.strategy ∧
      exclusionTerminalLaw reward excluded target.strategy =
        intendedTerminalLaw reward intended.strategy := by
  have below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excluded ≤ grossUtility reward (setup.parameterOutcome parameter terminal) who := by
    intro _ terminal _ who
    fin_cases who
    · exact low.trans (alice_gross_bounds nonnegative _).1
    · exact low.trans (bob_gross_bounds reward _).1
  obtain ⟨target, preserved, extends_, _, law⟩ :=
    setup.intended_sequentialEquilibrium_extends_to_exclusion finiteBindingTypes wellFormed
      parameter (grossUtility reward) (fun _ => excluded) below
      setup.intended_bounded.wellFoundedHistories setup.exclusion_bounded.wellFoundedHistories
      intended equilibrium
  exact ⟨target, preserved, extends_, law⟩

/-- For the concrete source game, the stated forfeit bounds give an actual
sequential equilibrium with no failed publications and an intended terminal law. -/
theorem exists_withholding_sequential_equilibrium {reward forfeit : ℝ}
    (nonnegative : 0 ≤ reward) (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit) :
    ∃ (intended : setup.intendedModel.BehavioralAssessment)
      (target : withholdingModel.BehavioralAssessment),
      intended.IsSequentialEquilibrium intended_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories (intendedPayoff reward) ∧
      target.IsSequentialEquilibrium (setup.decision_antichain _)
        withholding_bounded.wellFoundedHistories (withholdingPayoff reward forfeit) ∧
      (∀ final ∈ (withholdingModel.runBehavioralTerminalFrom
          withholding_bounded.wellFoundedHistories target.strategy
          withholdingProtocol.initHistory).support,
        ∀ terminal, setup.protocolReadout final.state = some terminal →
          ∀ who, failedReveals setup.program who (publicOutcome setup.program terminal) = 0) ∧
      withholdingTerminalLaw reward forfeit target.strategy =
        intendedTerminalLaw reward intended.strategy := by
  obtain ⟨intended, equilibrium⟩ := exists_intended_sequential_equilibrium reward
  obtain ⟨target, preserved, clean, law⟩ :=
    intended_equilibrium_preserved_under_withholding nonnegative coversAlice coversBob
      intended equilibrium
  exact ⟨intended, target, equilibrium, preserved, clean, law⟩

end Vegas.Examples.LateOpeningRuntimeSource
