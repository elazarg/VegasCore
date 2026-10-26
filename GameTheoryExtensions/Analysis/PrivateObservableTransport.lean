/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Protocol.PrivateStrategy
import GameTheoryExtensions.Math.InvariantObservables
import GameTheoryExtensions.Math.Probability.ObservableMoments

/-! # Closed observables for transcript-local adaptive policies

Observation-filtered action operators retain branch masses. Their invariant
space transports bounded terminal scores through the existing private-strategy
behavioral runner, for every policy on the actual input/output transcript.
Different systems can be represented by their disjoint union.
-/

noncomputable section

namespace GameTheory.Protocol.PrivateStrategy

open GameTheory.Math.Probability GameTheory.Math.InvariantObservables

variable {State Input Output : Type} [Finite State] [Finite Input] [Finite Output]

open Classical in
/-- An unnormalized observed branch of the actual action kernel. -/
def observedOperator (observe : State → Input) (advance : State → Output → PMF State)
    (label : Input × Output) : (State → ℝ) →ₗ[ℝ] (State → ℝ) where
  toFun value state := if observe state = label.1 then expect (advance state label.2) value else 0
  map_add' first second := by
    classical
    funext state
    dsimp
    split
    · exact expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    · simp
  map_smul' scalar value := by
    classical
    funext state
    dsimp
    split
    · exact expect_const_mul
    · simp

/-- The value of an actual adaptive continuation stays in every space closed
under all observed action branches. Only the terminal scores need be supplied. -/
theorem runBehavioral_value_mem
    (observe : State → Input) (advance : State → Output → PMF State)
    (space : Submodule ℝ (State → ℝ))
    (closed : ∀ label value, value ∈ space → observedOperator observe advance label value ∈ space)
    (policy : Transcript Input Output → Input → PMF Output)
    (payoff : State × Transcript Input Output → ℝ) (bound : ℝ)
    (bounded : ∀ result, |payoff result| ≤ bound)
    (terminal : ∀ past, (fun state => payoff (state, past)) ∈ space)
    (count : Nat) (past : Transcript Input Output) :
    (fun state => expect (runBehavioral policy observe advance count past state) payoff) ∈
      space := by
  classical
  let := Fintype.ofFinite State
  let := Fintype.ofFinite Input
  let := Fintype.ofFinite Output
  induction count generalizing past with
  | zero => simpa only [runBehavioral, expect_pure] using terminal past
  | succ count ih =>
      let value (input : Input) (output : Output) (state : State) :=
        expect (runBehavioral policy observe advance count ((input, output) :: past) state) payoff
      have representation :
          (fun state =>
            expect (runBehavioral policy observe advance (count + 1) past state) payoff) =
          ∑ input, ∑ output, (policy past input output).toReal •
            observedOperator observe advance (input, output) (value input output) := by
        funext state
        rw [runBehavioral, expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)]
        simp_rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, observedOperator,
          LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single (observe state)]
        · simp [expect, tsum_fintype, value]
        · intro input _ different
          simp [Ne.symm different]
        · simp
      rw [representation]
      exact space.sum_mem fun input _ => space.sum_mem fun output _ =>
        space.smul_mem _ (closed (input, output) _ (ih _))

/-- Equal initial moments on the closed space transport every adaptive policy's
terminal score, including scores that select a particular observation transcript.
Branch probabilities are retained rather than normalized away. -/
theorem expect_runBehavioral_eq_of_closed_observables
    (observe : State → Input) (advance : State → Output → PMF State)
    (space : Submodule ℝ (State → ℝ))
    (closed : ∀ label value, value ∈ space → observedOperator observe advance label value ∈ space)
    (source target : PMF State)
    (moments : ∀ value ∈ space, expect source value = expect target value)
    (policy : Transcript Input Output → Input → PMF Output)
    (payoff : State × Transcript Input Output → ℝ) (bound : ℝ)
    (bounded : ∀ result, |payoff result| ≤ bound)
    (terminal : ∀ past, (fun state => payoff (state, past)) ∈ space)
    (count : Nat) (past : Transcript Input Output) :
    expect (source.bind (runBehavioral policy observe advance count past)) payoff =
      expect (target.bind (runBehavioral policy observe advance count past)) payoff := by
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded),
    expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)]
  exact moments _ (runBehavioral_value_mem observe advance space closed policy payoff bound
    bounded terminal count past)

open Classical in
/-- Including the joint readout indicators upgrades moment transport to the
entire law of the selected readout and the player's full transcript. -/
theorem runBehavioral_joint_readout_eq_of_closed_observables {Readout : Type}
    (observe : State → Input) (advance : State → Output → PMF State)
    (space : Submodule ℝ (State → ℝ))
    (closed : ∀ label value, value ∈ space → observedOperator observe advance label value ∈ space)
    (source target : PMF State)
    (moments : ∀ value ∈ space, expect source value = expect target value)
    (readout : State → Readout)
    (indicators : ∀ outcome,
      (fun state => if readout state = outcome then (1 : ℝ) else 0) ∈ space)
    (policy : Transcript Input Output → Input → PMF Output)
    (count : Nat) (past : Transcript Input Output) :
    ((source.bind (runBehavioral policy observe advance count past)).map
        (fun result => (readout result.1, result.2))) =
      ((target.bind (runBehavioral policy observe advance count past)).map
        (fun result => (readout result.1, result.2))) := by
  classical
  apply PMF.ext
  intro result
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [toReal_map_apply, toReal_map_apply]
  have terminal (past : Transcript Input Output) :
      (fun state => if result = (readout state, past) then (1 : ℝ) else 0) ∈ space := by
    by_cases same : result.2 = past
    · convert indicators result.1 using 1
      funext state
      simp [Prod.ext_iff, same, eq_comm]
    · have zero :
          (fun state => if result = (readout state, past) then (1 : ℝ) else 0) = 0 := by
        funext state
        simp [Prod.ext_iff, same]
      rw [zero]
      exact space.zero_mem
  have transported := expect_runBehavioral_eq_of_closed_observables observe advance space closed
    source target moments policy
    (fun final => if result = (readout final.1, final.2) then (1 : ℝ) else 0) 1
    (by intro final; split <;> norm_num) terminal count past
  convert transported using 1 <;>
    apply expect_congr_on_support <;> intro final _ <;> split <;> simp_all

open Classical in
/-- A certificate on supplied columns suffices for every adaptive policy's
selected joint law. The only operator checks are on those columns. -/
theorem runBehavioral_joint_readout_eq_of_certificate {Readout Index : Type}
    (observe : State → Input) (advance : State → Output → PMF State)
    (basis : Index → State → ℝ)
    (closed : ∀ label index, observedOperator observe advance label (basis index) ∈
      Submodule.span ℝ (Set.range basis))
    (source target : PMF State)
    (moments : ∀ index, expect source (basis index) = expect target (basis index))
    (readout : State → Readout)
    (indicators : ∀ outcome, (fun state => if readout state = outcome then (1 : ℝ) else 0) ∈
      Submodule.span ℝ (Set.range basis))
    (policy : Transcript Input Output → Input → PMF Output)
    (count : Nat) (past : Transcript Input Output) :
    ((source.bind (runBehavioral policy observe advance count past)).map
        (fun result => (readout result.1, result.2))) =
      ((target.bind (runBehavioral policy observe advance count past)).map
        (fun result => (readout result.1, result.2))) :=
  runBehavioral_joint_readout_eq_of_closed_observables observe advance _
    (fun label _ => map_mem_span _ basis (closed label)) source target
    (fun _ => expect_eq_on_observable_span source target basis moments)
    readout indicators policy count past

end GameTheory.Protocol.PrivateStrategy
