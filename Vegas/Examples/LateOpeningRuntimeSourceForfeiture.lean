/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSourceEquilibrium
import Vegas.Game.ValueAdmissionPreservation

/-! # Failed bindings in the concrete source game

Every value-only withholding equilibrium extends to this full source
interface through the general commitment-admission theorem, preserving its
terminal-store and gross/forfeit payoff law. The source equilibrium may withhold
or fail reveals. This extension is valid for every real forfeit.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

abbrev forfeitingProtocol :=
  setup.executionProtocol (CommitmentInterface.forfeiture setup.program)

abbrev forfeitingModel :=
  setup.informationModel (CommitmentInterface.forfeiture setup.program)

theorem forfeiting_bounded : forfeitingProtocol.BoundedHorizon 4 :=
  setup.protocol_bounded _

def forfeitingPayoff (reward forfeit : ℝ) (who : Player)
    (history : forfeitingProtocol.History) : ℝ :=
  (setup.protocolReadout history.state).elim 0 (fun terminal =>
    forfeitUtility setup.program forfeit (grossUtility reward)
      (setup.parameterOutcome parameter terminal) who)

def forfeitingTerminalLaw (reward forfeit : ℝ)
    (profile : ∀ who, forfeitingModel.BehavioralPolicy who) :=
  (forfeitingModel.runBehavioralTerminalFrom
      forfeiting_bounded.wellFoundedHistories profile forfeitingProtocol.initHistory).map
    (fun final => (setup.protocolReadout final.state,
      fun who => forfeitingPayoff reward forfeit who final))

/-- Every value-only withholding equilibrium of this concrete program extends
to the interface admitting failed bindings, with exactly the same terminal store
and gross/forfeit payoffs, for every real forfeit. -/
theorem withholding_equilibrium_preserved_under_forfeiture (reward : ℝ) {forfeit : ℝ}
    (source : withholdingModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (setup.decision_antichain _)
      withholding_bounded.wellFoundedHistories (withholdingPayoff reward forfeit)) :
    ∃ target : forfeitingModel.BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _)
        forfeiting_bounded.wellFoundedHistories (forfeitingPayoff reward forfeit) ∧
      forfeitingTerminalLaw reward forfeit target.strategy =
        withholdingTerminalLaw reward forfeit source.strategy := by
  obtain ⟨target, sequential, _, _, historyLaw⟩ :=
    setup.values_sequentialEquilibrium_preserved (CommitmentInterface.forfeiture setup.program)
      finiteBindingTypes parameter (forfeitUtility setup.program forfeit (grossUtility reward))
      withholding_bounded.wellFoundedHistories forfeiting_bounded.wellFoundedHistories
      source equilibrium
  refine ⟨target, sequential, ?_⟩
  have projected := congrArg (PMF.map fun final =>
    (setup.protocolReadout final.state, fun who => forfeitingPayoff reward forfeit who final))
      historyLaw
  have state (history : withholdingProtocol.History) :
      ((setup.valuesRestriction (CommitmentInterface.forfeiture setup.program)).history
        history).state = history.state := rfl
  simpa only [forfeitingTerminalLaw, withholdingTerminalLaw, PMF.map_comp, Function.comp_def,
    forfeitingPayoff, withholdingPayoff, state] using projected.symm

/-- Every intended equilibrium of this initialized program has a full
forfeiture-source equilibrium with the same terminal store and payoffs. -/
theorem intended_equilibrium_preserved_under_forfeiture {reward forfeit : ℝ}
    (nonnegative : 0 ≤ reward) (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
      setup.intended_bounded.wellFoundedHistories (intendedPayoff reward)) :
    ∃ target : forfeitingModel.BehavioralAssessment,
      target.IsSequentialEquilibrium (setup.decision_antichain _)
        forfeiting_bounded.wellFoundedHistories (forfeitingPayoff reward forfeit) ∧
      forfeitingTerminalLaw reward forfeit target.strategy =
        intendedTerminalLaw reward intended.strategy := by
  obtain ⟨target, targetEquilibrium, _, sameLaw⟩ :=
    setup.intended_sequentialEquilibrium_preserved
      (CommitmentInterface.forfeiture setup.program) finiteBindingTypes wellFormed parameter
      (grossUtility reward) forfeit (grossUtility_range nonnegative coversAlice coversBob)
      setup.intended_bounded.wellFoundedHistories forfeiting_bounded.wellFoundedHistories
      intended equilibrium
  exact ⟨target, targetEquilibrium, sameLaw⟩

/-- The initialized Safe terminal-store and payoff law is a sequential
equilibrium outcome even when both bindings and publications can fail. -/
theorem exists_forfeiting_equilibrium_with_safe_law {reward forfeit : ℝ}
    (nonnegative : 0 ≤ reward) (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit) :
    ∃ assessment : forfeitingModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium (setup.decision_antichain _)
        forfeiting_bounded.wellFoundedHistories (forfeitingPayoff reward forfeit) ∧
      forfeitingTerminalLaw reward forfeit assessment.strategy = safeTerminalLaw reward := by
  obtain ⟨source, equilibrium, law⟩ :=
    exists_withholding_equilibrium_with_safe_law nonnegative coversAlice coversBob
  obtain ⟨target, sequential, sameLaw⟩ :=
    withholding_equilibrium_preserved_under_forfeiture reward source equilibrium
  exact ⟨target, sequential, sameLaw.trans law⟩

end Vegas.Examples.LateOpeningRuntimeSource
