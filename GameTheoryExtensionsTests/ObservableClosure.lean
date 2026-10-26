/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.PrivateObservableTransport

/-! # A computed observable space for an adaptive finite system

The state records a visible bit and an irrelevant hidden bit. Actions control
the next visible bit; the hidden bit flips. The two-dimensional observable
space identifies the joint law of the final visible bit and the entire actual
input/output transcript under every adaptive policy, despite different hidden
initial states. The observation filters are essential.
-/

noncomputable section

namespace GameTheoryExtensionsTests.ObservableClosure

open GameTheory.Protocol.PrivateStrategy GameTheory.Math.Probability
  GameTheory.Math.InvariantObservables

abbrev State := Bool × Bool

def observe (state : State) : Bool := state.1

def advance (state : State) (action : Bool) : PMF State := PMF.pure (action, !state.2)

/-- The two indicator columns returned by exact rational closure search. -/
def basis (bit : Bool) (state : State) : ℝ := if state.1 = bit then 1 else 0

def space : Submodule ℝ (State → ℝ) := Submodule.span ℝ (Set.range basis)

theorem basis_mem (bit : Bool) : basis bit ∈ space := Submodule.subset_span ⟨bit, rfl⟩

theorem operator_basis (label : Bool × Bool) (bit : Bool) :
    observedOperator observe advance label (basis bit) =
      (if label.2 = bit then (1 : ℝ) else 0) • basis label.1 := by
  funext state
  rcases state with ⟨visible, hidden⟩
  rcases label with ⟨input, output⟩
  cases visible <;> cases hidden <;> cases input <;> cases output <;> cases bit <;>
    norm_num [observedOperator, observe, advance, basis, expect_pure]

theorem closed (label : Bool × Bool) (value : State → ℝ) (member : value ∈ space) :
    observedOperator observe advance label value ∈ space := by
  apply map_mem_span (observedOperator observe advance label) basis ?_ member
  intro bit
  rw [operator_basis]
  exact space.smul_mem _ (basis_mem _)

theorem initial_moments (visible : Bool) (value : State → ℝ) (member : value ∈ space) :
    expect (PMF.pure (visible, false)) value = expect (PMF.pure (visible, true)) value := by
  apply expect_eq_on_observable_span _ _ basis ?_ member
  intro bit
  simp only [expect_pure, basis]

/-- The joint transcript/readout law agrees for every adaptive legal policy.
This includes information-dependent deviations, not just fixed action words. -/
theorem adaptive_joint_readout_eq
    (policy : Transcript Bool Bool → Bool → PMF Bool)
    (count : Nat) (past : Transcript Bool Bool) (visible : Bool) :
    (runBehavioral policy observe advance count past (visible, false)).map
        (fun result => (result.1.1, result.2)) =
      (runBehavioral policy observe advance count past (visible, true)).map
        (fun result => (result.1.1, result.2)) := by
  have transported := runBehavioral_joint_readout_eq_of_closed_observables
    observe advance space closed (PMF.pure (visible, false)) (PMF.pure (visible, true))
    (initial_moments visible) Prod.fst (by
      intro outcome
      convert basis_mem outcome using 1
      funext state
      cases first : state.1 <;> cases outcome <;> simp [basis, first]) policy count past
  simpa only [PMF.pure_bind] using transported

/-- The reduction loses actual hidden information, while preserving the
selected joint law proved above. -/
theorem hidden_laws_differ (visible : Bool) :
    (PMF.pure (visible, false) : PMF State) ≠ PMF.pure (visible, true) := by
  intro equal
  have atom := congrArg (fun law : PMF State => law (visible, false)) equal
  norm_num [PMF.pure_apply] at atom

abbrev FamilyState := Bool × State

/-- A disjoint pair of systems with independently chosen hidden transition
rates. The component tag is fixed and unavailable to the policy. -/
def familyAdvance (rate : Bool → Set.Icc (0 : ℝ) 1) (state : FamilyState) (action : Bool) :
    PMF FamilyState :=
  mix (rate state.1).1 (rate state.1).2.1 (rate state.1).2.2
    (PMF.pure (state.1, action, !state.2.2)) (PMF.pure (state.1, action, state.2.2))

def familyBasis (bit : Bool) (state : FamilyState) : ℝ := basis bit state.2

def familySpace : Submodule ℝ (FamilyState → ℝ) :=
  Submodule.span ℝ (Set.range familyBasis)

theorem familyBasis_mem (bit : Bool) : familyBasis bit ∈ familySpace :=
  Submodule.subset_span ⟨bit, rfl⟩

theorem family_operator_basis (rate : Bool → Set.Icc (0 : ℝ) 1)
    (label : Bool × Bool) (bit : Bool) :
    observedOperator (fun state : FamilyState => state.2.1) (familyAdvance rate) label
        (familyBasis bit) =
      (if label.2 = bit then (1 : ℝ) else 0) • familyBasis label.1 := by
  classical
  funext state
  simp only [observedOperator, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.smul_apply, smul_eq_mul]
  rw [familyAdvance, expect_mix_of_finite, expect_pure, expect_pure]
  by_cases observed : state.2.1 = label.1 <;> by_cases chosen : label.2 = bit <;>
    simp [familyBasis, basis, observed, chosen]

/-- One symbolic closure certificate works for both hidden kernels at every
parameter. Consequently arbitrary common approximation sequences and adaptive
policies retain the entire selected joint law, not just one parameter's moments. -/
theorem parameter_uniform_adaptive_joint_readout_eq
    (rate : Bool → Set.Icc (0 : ℝ) 1)
    (policy : Transcript Bool Bool → Bool → PMF Bool)
    (count : Nat) (past : Transcript Bool Bool) (visible : Bool) :
    (runBehavioral policy (fun state : FamilyState => state.2.1) (familyAdvance rate)
        count past (false, visible, false)).map
        (fun result => (result.1.2.1, result.2)) =
      (runBehavioral policy (fun state : FamilyState => state.2.1) (familyAdvance rate)
        count past (true, visible, true)).map
        (fun result => (result.1.2.1, result.2)) := by
  have transported := runBehavioral_joint_readout_eq_of_certificate
    (fun state : FamilyState => state.2.1) (familyAdvance rate) familyBasis (by
      intro label bit
      rw [family_operator_basis]
      exact familySpace.smul_mem _ (familyBasis_mem _))
    (PMF.pure (false, visible, false)) (PMF.pure (true, visible, true))
    (by intro bit; simp only [expect_pure, familyBasis, basis])
    (fun state => state.2.1) (by
      intro outcome
      have member : familyBasis outcome ∈ Submodule.span ℝ (Set.range familyBasis) :=
        familyBasis_mem outcome
      convert member using 1
      funext state
      cases first : state.2.1 <;> cases outcome <;> simp [familyBasis, basis, first])
    policy count past
  simpa only [PMF.pure_bind] using transported

end GameTheoryExtensionsTests.ObservableClosure
