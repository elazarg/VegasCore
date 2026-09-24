/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DecisionPayoff

/-! # Fixed payoffs permit some genuinely lossy observations

The hidden bit affects the payoff amount but never the optimal action in the
positive example. Changing to the fixed correct-report payoff makes the same
observation erasure fail, even when the target strategy may depend on that payoff.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ObservationPayoff

open GameTheory.DecisionExperiment GameTheory.Math.Probability

def prior : FinDist Bool := FinDist.uniformOfFintype

def reward (state action : Bool) : ℝ :=
  if action then (if state then 2 else 1) else 0

theorem hidden_bit_changes_reward : reward false true ≠ reward true true := by
  norm_num [reward]

theorem common_action : HasCommonMaximizer prior (fun _ => ()) reward := by
  intro signal
  refine ⟨true, ?_⟩
  intro state _ _ alternative
  cases state <;> cases alternative <;> norm_num [reward]

/-- Every abstract optimum is implementable for this payoff despite erasing a
supported, payoff-relevant bit. No payoff-specific strategy search is needed. -/
theorem preserves_reward :
    ∀ source : Unit → FinDist Bool,
      IsBayesOptimal prior (fun _ => ()) reward source →
      ∃ target : Bool → FinDist Bool,
        IsBayesOptimal prior id reward target ∧
        resultLaw prior id id target = resultLaw prior (fun _ => ()) id source :=
  (preserves_fixed_payoff_iff_commonMaximizer prior (fun _ => ()) id reward).mpr common_action

theorem reporting_has_no_common_action :
    ¬ HasCommonMaximizer prior (fun _ => ()) (reportUtility (id : Bool → Bool)) := by
  rintro common
  obtain ⟨action, optimal⟩ := common ()
  cases action with
  | false =>
    have impossible := optimal true (FinDist.mem_support_uniformOfFintype true) rfl true
    norm_num [reportUtility] at impossible
  | true =>
    have impossible := optimal false (FinDist.mem_support_uniformOfFintype false) rfl false
    norm_num [reportUtility] at impossible

/-- Constant payoffs preserve source equilibria, but do not imply equality of
the two sets of equilibrium outcome laws: the informed player can correlate
its action with the bit. -/
theorem constant_payoff_extra_informed_law :
    IsBayesOptimal prior id (fun _ _ : Bool => (0 : ℝ)) FinDist.pure ∧
      ∀ source : Unit → FinDist Bool,
        resultLaw prior id id FinDist.pure ≠ resultLaw prior (fun _ => ()) id source := by
  refine ⟨?_, ?_⟩
  · intro signal alternative
    simp [localValue, FinDist.expect_const]
  · intro source
    apply no_optimal_report_law_match prior (fun _ => ()) id id
      (fun _ _ _ _ same => same)
      (FinDist.mem_support_uniformOfFintype false)
      (FinDist.mem_support_uniformOfFintype true) rfl Bool.false_ne_true source FinDist.pure
    rw [fullInformation_optimal_iff]
    intro state _ action
    simp only [FinDist.expect_pure, reportUtility, id_eq, ↓reduceIte]
    split <;> norm_num

open Protocol in
/-- Fixing the correct-report payoff still permits a sequential-equilibrium
outcome impossibility; a utility-dependent translator cannot repair it. -/
theorem fixed_reporting_payoff_not_preserved :
    ¬ (∀ source : (model (Action := Bool) prior (fun _ => ())).BehavioralAssessment,
      source.IsSequentialEquilibriumFor (antichain prior (fun _ => ()))
        (fun _ site => source.continuationContext site
          (fun history => payoff (reportUtility (id : Bool → Bool)) history.state) 2) →
      ∃ target : (model (Action := Bool) prior id).BehavioralAssessment,
        target.IsSequentialEquilibriumFor (antichain prior id)
          (fun _ site => target.continuationContext site
            (fun history => payoff (reportUtility (id : Bool → Bool)) history.state) 2) ∧
        observedLaw prior id id target = observedLaw prior (fun _ => ()) id source) := by
  intro preserves
  exact reporting_has_no_common_action
    ((preserves_fixed_payoff_sequentialEquilibria_iff_commonMaximizer prior (fun _ => ())
      id (reportUtility (id : Bool → Bool))).mp preserves)

end GameTheoryExtensionsTests.ObservationPayoff
