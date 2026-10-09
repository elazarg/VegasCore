/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBindingPrefix

/-! # Native binding beliefs from actual conditional execution probabilities

Every compatible raw history belongs to the same checked physical prefix at
Bob's fresh binding decision. Bayes beliefs of any hidden-state readout are
therefore actual joint prefix probabilities divided by the information mass.
Sequential consistency supplies one common fully mixed sequence along which
all these ratios converge, including observations whose mass tends to zero.
No belief at an unreached decision is chosen independently of that sequence.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBindingPosterior

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBindingPrefix

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (execution : app.Execution)
  (current : representative.1.state = some ⟨14, some bob, execution⟩)
  (ready : execution.application.config.cut.Ready bobBindEvent)

def readoutBelief {Label : Type}
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (readout : app.ProtocolState → Label) (value : Label) : ℝ :=
  InformationModel.finiteHistoryBelief assessment bob site
    (readoutHistories weight nonnegative site readout value)

def conditionalPrefixProbability {Label : Type}
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (readout : app.ProtocolState → Label) (value : Label) : ℝ :=
  ((bindingPrefix weight nonnegative profile).toOuterMeasure
    {state | app.observe bob state = site.1 ∧ readout state = value}).toReal /
      ((bindingPrefix weight nonnegative profile).toOuterMeasure
        {state | app.observe bob state = site.1}).toReal

include current ready in
theorem information_probability_positive
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) :
    0 < ((bindingPrefix weight nonnegative assessment.strategy).toOuterMeasure
      {state | app.observe bob state = site.1}).toReal := by
  rw [← information_mass_eq_prefix weight nonnegative site representative execution current ready]
  exact ENNReal.toReal_pos
    (ne_of_gt ((LateOpeningRuntimeNash.model weight nonnegative).informationMass_pos_of_fullSupport
      assessment.strategy mixed bob site))
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      ((LateOpeningRuntimeNash.model weight nonnegative).informationMass_le_one
        assessment.strategy bob site
        (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) bob site)))

include current ready in
theorem bayes_readout_belief_eq_conditional_probability {Label : Type}
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (bayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (LateOpeningRuntimeNash.model weight nonnegative) assessment
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)))
    (readout : app.ProtocolState → Label) (value : Label) :
    readoutBelief weight nonnegative site assessment readout value =
      conditionalPrefixProbability weight nonnegative site assessment.strategy readout value := by
  unfold readoutBelief conditionalPrefixProbability
  rw [InformationModel.finiteHistoryBelief_eq_div_reach
    (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)) bayes bob site
    ((LateOpeningRuntimeNash.model weight nonnegative).informationMass_pos_of_fullSupport
      assessment.strategy mixed bob site),
    finite_history_reach_eq_prefix weight nonnegative site representative execution current ready,
    information_mass_eq_prefix weight nonnegative site representative execution current ready]

include current ready in
theorem conditional_probability_tendsto {Label : Type}
    (sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (mixed : ∀ n, (sequence n).IsFullyMixed)
    (bayes : ∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
      (LateOpeningRuntimeNash.model weight nonnegative) (sequence n)
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)))
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (readout : app.ProtocolState → Label) (value : Label) :
    Tendsto (fun n => conditionalPrefixProbability weight nonnegative site
      (sequence n).strategy readout value) atTop
        (nhds (readoutBelief weight nonnegative site assessment readout value)) := by
  have limit := InformationModel.finiteHistoryBelief_tendsto converges bob site
    (readoutHistories weight nonnegative site readout value)
  apply limit.congr'
  exact Filter.Eventually.of_forall fun n =>
    bayes_readout_belief_eq_conditional_probability weight nonnegative site representative
      execution current ready (sequence n) (mixed n) (bayes n) readout value

include current ready in
/-- A single native consistency witness determines all readout posteriors.
There is no positive lower bound on the limiting information probability. -/
theorem consistent_conditional_probabilities {Label : Type}
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))) :
    ∃ sequence : ℕ → (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed ∧
        InformationModel.BehavioralAssessment.IsBayesConsistent
          (LateOpeningRuntimeNash.model weight nonnegative) (sequence n)
          (rawMenu.decisionInformationAntichain initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative))) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment ∧
      ∀ (readout : app.ProtocolState → Label) (value : Label),
        Tendsto (fun n => conditionalPrefixProbability weight nonnegative site
          (sequence n).strategy readout value) atTop
            (nhds (readoutBelief weight nonnegative site assessment readout value)) := by
  obtain ⟨sequence, approximate, converges⟩ := consistent
  refine ⟨sequence, approximate, converges, ?_⟩
  intro readout value
  exact conditional_probability_tendsto weight nonnegative site representative execution current
    ready sequence assessment (fun n => (approximate n).1) (fun n => (approximate n).2)
      converges readout value

end Vegas.Examples.LateOpeningRuntimeBindingPosterior
