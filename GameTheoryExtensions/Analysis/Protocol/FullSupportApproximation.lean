/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheory.Protocol.DecisionPlan
import Mathlib.Probability.Distributions.Uniform

/-! # Full support beyond actual decision sites

Consistency constrains strategy coordinates only at genuine decision sites.
Finite unused menus can be trembled independently toward the prescribed policy;
agreement at decisions preserves every actual history weight and Bayes belief.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)

/-- A finite-menu consistent assessment admits one common Bayes approximation
with full support and prescribed strategy convergence at every information state. -/
theorem BehavioralAssessment.IsSequentiallyConsistent.exists_everywhere_full
    [∀ who info, Finite (M.Choice who info)]
    {assessment : M.BehavioralAssessment} {antichain : M.DecisionInformationAntichain}
    (consistent : assessment.IsSequentiallyConsistent antichain) :
    ∃ sequence : Nat → M.BehavioralAssessment,
      (∀ n who info choice, choice ∈ ((sequence n).strategy who info).support) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent M (sequence n) antichain) ∧
      (∀ who info, PMFConvergesPointwise (fun n => (sequence n).strategy who info)
        (assessment.strategy who info)) ∧
      BehavioralAssessmentConvergesPointwise sequence assessment := by
  classical
  let : ∀ who info, Fintype (M.Choice who info) := fun who info => Fintype.ofFinite _
  obtain ⟨original, valid, converges⟩ := consistent
  let weight := fun n : Nat => 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp only [weight]; positivity
  have atMostOne (n : Nat) : weight n ≤ 1 := by
    dsimp only [weight]
    exact (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let uniform : ∀ who, M.BehavioralPolicy who := fun who info => by
    let : Nonempty (M.Choice who info) := ⟨(assessment.strategy who info).support_nonempty.choose⟩
    exact PMF.uniformOfFintype _
  let profile := fun n who info => if M.IsDecisionInfo who info then
    (original n).strategy who info else
      mix (weight n) (positive n).le (atMostOne n) (uniform who info)
        (assessment.strategy who info)
  let sequence : Nat → M.BehavioralAssessment := fun n =>
    ⟨profile n, (original n).belief⟩
  have agrees (n : Nat) (who : ι) :
      ((sequence n).strategy who).AgreesAtDecisions ((original n).strategy who) := by
    funext site
    exact ite_eq_left site.2
  have reach (n : Nat) (history : E.History) :
      M.historyReachWeight (sequence n).strategy history =
        M.historyReachWeight (original n).strategy history := by
    change (M.runBehavioralFrom (sequence n).strategy history.trace.length E.initHistory)
      history =
      (M.runBehavioralFrom (original n).strategy history.trace.length E.initHistory) history
    exact congrArg (fun law => law history)
      (M.runBehavioralFrom_eq_of_agreesAtDecisions (agrees n) history.trace.length E.initHistory)
  have mass (n : Nat) (who : ι) (site : M.InformationSite who) :
      M.informationMass (sequence n).strategy who site =
        M.informationMass (original n).strategy who site :=
    tsum_congr fun history => reach n history.1
  have allConverges (who : ι) (info : M.InfoState who) :
      PMFConvergesPointwise (fun n => (sequence n).strategy who info)
        (assessment.strategy who info) := by
    by_cases decision : M.IsDecisionInfo who info
    · simpa only [sequence, profile, ite_eq_left decision] using
        converges.strategy who ⟨info, decision⟩
    · simpa only [sequence, profile, ite_eq_right decision] using
        pmfConvergesPointwise_mix_zero weight (fun n => (positive n).le) atMostOne
          tendsto_one_div_add_atTop_nhds_zero_nat (uniform who info)
          (assessment.strategy who info)
  refine ⟨sequence, ?_, ?_, allConverges,
    ⟨fun who site => allConverges who site.1, converges.2⟩⟩
  · intro n who info choice
    by_cases decision : M.IsDecisionInfo who info
    · change choice ∈ (profile n who info).support
      rw [show profile n who info = (original n).strategy who info from ite_eq_left decision]
      exact (valid n).1 who ⟨info, decision⟩ choice
    · change choice ∈ (profile n who info).support
      rw [show profile n who info = mix _ _ _ _ _ from ite_eq_right decision]
      apply mem_support_mix_left (weight n) (positive n).le (atMostOne n) (positive n)
      let : Nonempty (M.Choice who info) :=
        ⟨(assessment.strategy who info).support_nonempty.choose⟩
      exact PMF.mem_support_uniformOfFintype choice
  · intro n who site positiveMass history
    change (original n).belief who site history = _
    rw [reach, mass]
    exact (valid n).2 who site ((mass n who site) ▸ positiveMass) history

end GameTheory.Protocol.InformationModel
