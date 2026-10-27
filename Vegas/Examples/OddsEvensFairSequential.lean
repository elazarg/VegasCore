/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensFairProfile
import GameTheory.Analysis.Protocol.InformationLocalization

/-! # Root indifference certifies the uniform Odds–Evens assessment -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

def terminalUtility (who : Player) (final : setup.intendedProtocol.History) : ℝ :=
  (setup.protocolReadout final.state).elim 0
    (fun terminal => sourceUtility (setup.parameterOutcome (fun _ => ()) terminal) who)

/-- All actual information sites are reached by the uniform-bit strategy.
Thus root indifference against whole behavioral deviations supplies sequential
rationality, with the canonical Bayesian beliefs and constant full-support
consistency witness. -/
theorem uniformAssessment_equilibrium_of_rootValue
    (rootValue : ∀ who (deviation : setup.intendedModel.BehavioralPolicy who),
      expect (setup.intendedModel.runBehavioral
        (Profile.update (sig := setup.intendedModel.behavioralSignature)
          uniformProfile who deviation)
        (instructionCount setup.program + 1))
        (terminalUtility who) = 100) :
    uniformAssessment.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories terminalUtility := by
  classical
  let : Fintype setup.intendedProtocol.History := Fintype.ofFinite _
  let certificate := setup.intended_bounded.wellFoundedHistories
  have terminalValue (who : Player) (deviation : setup.intendedModel.BehavioralPolicy who) :
      expect (setup.intendedModel.runBehavioralTerminalFrom certificate
        (Profile.update (sig := setup.intendedModel.behavioralSignature)
          uniformProfile who deviation)
        setup.intendedProtocol.initHistory)
        (terminalUtility who) = 100 := by
    rw [setup.intendedModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      certificate setup.intended_bounded]
    exact rootValue who deviation
  have baseline (who : Player) :
      expect (setup.intendedModel.runBehavioralTerminalFrom certificate uniformProfile
        setup.intendedProtocol.initHistory) (terminalUtility who) = 100 := by
    simpa only [Profile.update_eq_self] using terminalValue who (uniformProfile who)
  have rootComparison (who : Player) (deviation : setup.intendedModel.BehavioralPolicy who) :
      (setup.intendedModel.behavioralRootComparison certificate id uniformAssessment.strategy
        who deviation).Holds (terminalUtility who) := by
    apply (IncentiveComparison.holds_iff _ _).mpr
    simp only [behavioralRootComparison, PMF.map_id]
    change expect (setup.intendedModel.runBehavioralTerminalFrom certificate
      (Profile.update (sig := setup.intendedModel.behavioralSignature) uniformProfile who deviation)
      setup.intendedProtocol.initHistory)
        (terminalUtility who) ≤
      expect (setup.intendedModel.runBehavioralTerminalFrom certificate uniformProfile
        setup.intendedProtocol.initHistory) (terminalUtility who)
    rw [terminalValue, baseline]
  have bayes : BehavioralAssessment.IsBayesConsistent setup.intendedModel uniformAssessment
      setup.intendedModel_decisionRecall.decisionInformationAntichain :=
    setup.intendedModel.bayesAssessment_isBayesConsistent uniformProfile
      (fun who site => uniformProfile_fullSupport who site.1) setup.intended_decision_antichain
  have positive (who : Player) (site : setup.intendedModel.InformationSite who) :
      0 < setup.intendedModel.informationMass uniformAssessment.strategy who site :=
    setup.intendedModel.informationMass_pos_of_fullSupport uniformProfile
      (fun actor atSite => uniformProfile_fullSupport actor atSite.1) who site
  have comparisons := setup.intendedModel.implies_assessment_of_decisionRecall certificate id
    uniformAssessment setup.intendedModel_decisionRecall bayes positive
    (fun final who => terminalUtility who final) rootComparison
  refine ⟨?_, uniformAssessment_consistent⟩
  exact (setup.intendedModel.isSequentiallyRational_iff_holds certificate id uniformAssessment
    (fun final who => terminalUtility who final)).mpr comparisons

end Vegas.Examples.OddsEvens
