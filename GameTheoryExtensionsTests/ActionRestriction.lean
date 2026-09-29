/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationPayoff
import GameTheoryExtensionsTests.ContinuationDecision

/-! # Removing an action is different from assigning it probability zero

Use the existing terminal protocol with one state and payoff zero for `false`,
one for `true`. Keeping just one action gives an SE for either singleton menu.
Restoring both actions makes the `false` outcome impossible at every SE.
The optimal full-game assessment itself assigns probability zero to `false`.
The failed lift is nevertheless sequentially consistent: rationality, rather
than a full-support requirement on the limit strategy, is what fails.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ActionRestriction

open GameTheory GameTheory.Protocol GameTheory.DecisionExperiment
open GameTheory.DecisionExperiment.Protocol GameTheory.Math.Probability

def prior : PMF Unit := PMF.pure ()

def reward (_ : Unit) (action : Bool) : ℝ := if action then 1 else 0

abbrev Retained (keep : Bool) := {action : Bool // action = keep}

instance (keep : Bool) : Nonempty (Retained keep) := ⟨⟨keep, rfl⟩⟩

def restricted (keep : Bool) : (model (Action := Retained keep) prior id).BehavioralAssessment :=
  assessment prior id (fun _ => PMF.pure ⟨keep, rfl⟩)

/-- Deleting an available action changes the game, even with no hidden
information, no off-path decision sites, and a fixed payoff. -/
theorem restricted_equilibrium (keep : Bool) :
    (restricted keep).IsSequentialEquilibriumFor (antichain prior id)
      (fun _ site => (restricted keep).continuationContext site
        (fun history => payoff (fun state action => reward state action.1) history.state) 2) := by
  apply (isSequentialEquilibrium_iff prior id _ _).mpr
  rw [fullInformation_optimal_iff]
  refine ⟨fun _ => ResponseIntegrable.of_finite _ _ _, fun state _ action => ?_⟩
  simp only [expect_pure, action.property, le_refl]

theorem restricted_outcome (keep : Bool) :
    (observedLaw prior id id (restricted keep)).map
        (fun result => (result.1, result.2.val)) = PMF.pure ((), keep) := by
  simp [observedLaw_eq, restricted, assessment, response_policy, resultLaw_eq_bind, prior,
    PMF.pure_map]

def restored (keep : Bool) : (model (Action := Bool) prior id).BehavioralAssessment :=
  assessment prior id (fun _ => PMF.pure keep)

theorem restored_consistent (keep : Bool) :
    (restored keep).IsSequentiallyConsistent (antichain prior id) :=
  assessment_consistent prior id _

theorem restored_equilibrium_iff (keep : Bool) :
    (restored keep).IsSequentialEquilibriumFor (antichain prior id)
      (fun _ site => (restored keep).continuationContext site
        (fun history => payoff reward history.state) 2) ↔ keep = true := by
  rw [restored, isSequentialEquilibrium_iff, fullInformation_optimal_iff]
  constructor
  · intro optimal
    have bound := optimal.2 () ((PMF.mem_support_pure_iff _ _).mpr rfl) true
    cases keep <;> norm_num [reward, expect_pure] at *
  · rintro rfl
    refine ⟨fun _ => ResponseIntegrable.of_finite _ _ _, fun state _ action => ?_⟩
    cases action <;> norm_num [reward, expect_pure]

/-- A standard SE may give a legal action exactly zero probability. Its
consistency proof uses fully mixed approximating profiles in the full game. -/
theorem equilibrium_with_zero_probability_action :
    (restored true).IsSequentialEquilibriumFor (antichain prior id)
        (fun _ site => (restored true).continuationContext site
          (fun history => payoff reward history.state) 2) ∧
      ((response prior id ((restored true).strategy ()) ()) false).toReal = 0 ∧
      (arena (Action := Bool) prior).Legal (.decision ()) (fun _ => some false) := by
  refine ⟨(restored_equilibrium_iff true).mpr rfl, ?_, decision_legal prior () false⟩
  simp [restored, assessment, response_policy, PMF.pure_apply]

def decision : (model (Action := Bool) prior id).ContinuationDecision
    (fun _ history => payoff reward history.state) 2 Unit Bool :=
  GameTheoryExtensionsTests.ContinuationDecision.decision prior id
    (site prior id () ((PMF.mem_support_pure_iff _ _).mpr rfl)) reward

theorem expected_reward (original : (model (Action := Bool) prior id).BehavioralAssessment)
    (action : Bool) : decision.expectedReward original action = reward () action := by
  simp [InformationModel.ContinuationDecision.expectedReward, decision, reward,
    GameTheoryExtensionsTests.ContinuationDecision.decision, expect_constant]

theorem restored_response (keep : Bool) :
    decision.response (restored keep).strategy = PMF.pure keep := by
  change response prior id (policy prior id (fun _ => PMF.pure keep)) _ = _
  rw [response_policy]

/-- The zero-probability better action still defeats rationality. This
failure holds although the proposed full-game assessment is consistent. -/
theorem zero_probability_is_not_deletion :
    (restored false).IsSequentiallyConsistent (antichain prior id) ∧
      ((decision.response (restored false).strategy) true).toReal = 0 ∧
      ¬ (restored false).IsSequentiallyRationalWithin
        (fun _ history => payoff reward history.state) 2 := by
  refine ⟨restored_consistent false, ?_, ?_⟩
  · rw [restored_response]
    simp [PMF.pure_apply]
  · apply decision.not_rational_of_supported_inferior (restored false) false true
    · rw [restored_response]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    · norm_num [expected_reward, reward]

/-- The positive omission certificate applies to the same full-game decision:
retaining `true` suffices because `false` is dominated at every history. -/
theorem dominated_omission_rational :
    (restored true).IsSequentiallyRationalAt decision.site
      ((restored true).continuationContext decision.site
        (fun history => payoff reward history.state) 2) := by
  apply decision.rationalAt_of_omitted_dominated (restored true) {true}
  · intro action kept
    have same : action = true := Set.mem_singleton_iff.mp kept
    rw [same, restored_response, expect_pure]
  · intro action omitted
    refine ⟨true, rfl, fun _ => ?_⟩
    cases action <;>
      norm_num [decision, GameTheoryExtensionsTests.ContinuationDecision.decision, reward]

/-- No strategy or belief repair can preserve the removed-action game's
`false` outcome when `true` is restored as an available alternative. -/
theorem no_equilibrium_with_restricted_false_outcome
    (target : (model (Action := Bool) prior id).BehavioralAssessment)
    (equilibrium : target.IsSequentialEquilibriumFor (antichain prior id)
      (fun _ site => target.continuationContext site
        (fun history => payoff reward history.state) 2)) :
    observedLaw prior id id target ≠ PMF.pure ((), false) := by
  intro same
  have responseEq := congrArg (fun law : PMF (Unit × Bool) => law.map Prod.snd) same
  simp only [observedLaw_eq, resultLaw_eq_bind, prior, PMF.pure_bind, id_eq,
    PMF.map_comp, Function.comp_def, PMF.pure_map] at responseEq
  change (response prior id (target.strategy ()) ()).map id = PMF.pure false at responseEq
  rw [PMF.map_id] at responseEq
  have optimal := optimal_of_sequentialEquilibrium prior id target reward equilibrium
  have bound := ((fullInformation_optimal_iff prior reward _).mp optimal).2 ()
    ((PMF.mem_support_pure_iff _ _).mpr rfl) true
  rw [responseEq] at bound
  norm_num [reward, expect_pure] at bound

end GameTheoryExtensionsTests.ActionRestriction
