/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.ObservationAbstraction
import GameTheoryExtensions.Analysis.Protocol.DecisionExperiment

/-! # Exhaustive observation quotients of a four-observation decision

The outcome-relevant fact separates observations `0, 1` from `2, 3`.
All deterministic maps to four labels are enumerated, including unused labels.
`retainsFact` classifies whether an observer can recover that fact. The counts
are checked by the kernel; no external solver or native computation axiom is
used. This finite experiment is not an enumeration of arbitrary game abstractions.
-/

namespace GameTheoryExtensionsTests.ObservationQuotients

open GameTheory.DecisionExperiment GameTheory.Math.Probability

abbrev Observation := Fin 4

def fact (observation : Observation) : Bool := decide (observation.val < 2)

abbrev QuotientMap := Observation → Observation

def retainsFact (quotient : QuotientMap) : Prop :=
  ∀ first second, quotient first = quotient second → fact first = fact second

instance (quotient : QuotientMap) : Decidable (retainsFact quotient) :=
  inferInstanceAs (Decidable (∀ first second,
    quotient first = quotient second → fact first = fact second))

/-- Label blocks by their order of first appearance in the observation list. -/
def canonical (quotient : QuotientMap) : Prop :=
  quotient 0 = 0 ∧ (quotient 1).val ≤ 1 ∧
    (quotient 2).val ≤ (quotient 1).val + 1 ∧
    (quotient 3).val ≤ max (quotient 1).val (quotient 2).val + 1

instance (quotient : QuotientMap) : Decidable (canonical quotient) :=
  inferInstanceAs (Decidable (quotient 0 = 0 ∧ (quotient 1).val ≤ 1 ∧
    (quotient 2).val ≤ (quotient 1).val + 1 ∧
    (quotient 3).val ≤ max (quotient 1).val (quotient 2).val + 1))

theorem all_maps_count : Fintype.card QuotientMap = 256 := by
  simp [QuotientMap, Observation]

theorem fact_retaining_maps_count :
    (Finset.univ.filter retainsFact).card = 84 := by decide

theorem canonical_maps_count :
    (Finset.univ.filter canonical).card = 15 := by decide

theorem fact_retaining_canonical_maps_count :
    (Finset.univ.filter fun quotient => canonical quotient ∧ retainsFact quotient).card = 4 :=
  by decide

/-- Any deterministic observation of these four states has the same information
partition as one of the 256 enumerated maps, even with an infinite signal type. -/
theorem finite_labels_complete {Signal : Type*} (observe : Observation → Signal) :
    ∃ quotient : QuotientMap,
      ∀ first second, quotient first = quotient second ↔ observe first = observe second := by
  classical
  let representative (signal : Signal) : Observation :=
    if present : ∃ state, observe state = signal then present.choose else 0
  have represents (state : Observation) :
      observe (representative (observe state)) = observe state := by
    have present : ∃ other, observe other = observe state := ⟨state, rfl⟩
    simpa only [representative, dite_eq_left present] using present.choose_spec
  refine ⟨fun state => representative (observe state), fun first second => ⟨?_, ?_⟩⟩
  · intro same
    calc
      observe first = observe (representative (observe first)) := (represents first).symm
      _ = observe (representative (observe second)) := congrArg observe same
      _ = observe second := represents second
  · intro same
    exact congrArg representative same

/-- The actual missing information is exposed, not just a failed Boolean check. -/
theorem rejected_map_has_collision (quotient : QuotientMap)
    (rejected : ¬ retainsFact quotient) :
    ∃ first second, quotient first = quotient second ∧ fact first ≠ fact second := by
  simp only [retainsFact] at rejected
  push Not at rejected
  exact rejected

noncomputable def prior : FinDist Observation := FinDist.uniformOfFintype

/-- The executable criterion is exactly the checked information condition. -/
theorem retainsFact_iff_perfect_report (quotient : QuotientMap) :
    retainsFact quotient ↔
      ∃ policy, value prior quotient (reportUtility fact) policy = 1 := by
  rw [exists_perfect_report_iff,
    determines_iff_of_fullSupport prior FinDist.mem_support_uniformOfFintype]
  rfl

/-- The exhaustive counts also classify preservation of every optimum for
every utility on the retained fact and report, allowing arbitrary translations. -/
theorem retainsFact_iff_preserves_all_optima (quotient : QuotientMap) :
    retainsFact quotient ↔
      (∀ utility : Bool → Bool → ℝ, ∀ source : Observation → FinDist Bool,
        IsBayesOptimal prior quotient (fun state => utility (fact state)) source →
          ∃ target : Observation → FinDist Bool,
            IsBayesOptimal prior id (fun state => utility (fact state)) target ∧
              resultLaw prior id fact target = resultLaw prior quotient fact source) := by
  rw [preserves_all_optima_iff_determines,
    determines_iff_of_fullSupport prior FinDist.mem_support_uniformOfFintype]
  rfl

open GameTheory.DecisionExperiment.Protocol in
/-- The same finite enumeration classifies actual sequential-equilibrium
outcome implementability, including every consistent belief assessment. -/
theorem retainsFact_iff_preserves_all_sequentialEquilibria (quotient : QuotientMap) :
    retainsFact quotient ↔
      (∀ utility : Bool → Bool → ℝ,
        ∀ source : (model (Action := Bool) prior quotient).BehavioralAssessment,
          source.IsSequentialEquilibriumFor (antichain prior quotient)
            (fun _ site => source.continuationContext site
              (fun history => payoff (fun state => utility (fact state)) history.state) 2) →
          ∃ target : (model (Action := Bool) prior id).BehavioralAssessment,
            target.IsSequentialEquilibriumFor (antichain prior id)
              (fun _ site => target.continuationContext site
                (fun history => payoff (fun state => utility (fact state)) history.state) 2) ∧
            observedLaw prior id fact target = observedLaw prior quotient fact source) := by
  rw [preserves_all_sequentialEquilibria_iff_determines,
    determines_iff_of_fullSupport prior FinDist.mem_support_uniformOfFintype]
  rfl

/-- Every rejected map has an optimal coarse policy whose outcome law differs
from every informed optimum. This covers all randomized policies, not just the
finite maps enumerated above. It is a terminal-decision optimality theorem. -/
theorem rejected_map_no_optimal_outcome_match (quotient : QuotientMap)
    (rejected : ¬ retainsFact quotient) :
    ∃ source : Observation → FinDist Bool,
      IsBayesOptimal prior quotient (reportUtility fact) source ∧
      ∀ target : Observation → FinDist Bool,
        IsBayesOptimal prior id (reportUtility fact) target →
          (outcomeLaw prior id target).map (fun result => (fact result.1, result.2)) ≠
            (outcomeLaw prior quotient source).map (fun result => (fact result.1, result.2)) := by
  obtain ⟨first, second, same, different⟩ := rejected_map_has_collision quotient rejected
  exact exists_optimal_no_report_law_match prior quotient id fact
    (fun _ _ _ _ same => congrArg fact same)
    (FinDist.mem_support_uniformOfFintype first)
    (FinDist.mem_support_uniformOfFintype second) same different

end GameTheoryExtensionsTests.ObservationQuotients
