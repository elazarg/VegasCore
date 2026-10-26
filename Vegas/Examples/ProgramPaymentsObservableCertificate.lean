/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.ProgramPaymentsFiniteRuntime

/-! # A stopped observable certificate for the compiled payment program

Only the four genuine callback observations label continuation operators.
Terminal rows are zero: the certificate does not observe a private terminal
binding after the last instruction. The selected readout is the joint original
publication, monetary transfer and utility.
-/

noncomputable section

namespace Vegas.Examples.ProgramPaymentsObservableCertificate

open ProgramPaymentsFiniteRuntime
open GameTheory.Protocol.PrivateStrategy GameTheory.Math.InvariantObservables
open GameTheory.Math.Probability

inductive Code where
  | initial
  | bound (binding : PublicationResult Bool)
  | finished (publication : PublicationResult Bool)
  deriving DecidableEq, Fintype

def code : ConfigCode → Code
  | .initial => .initial
  | .bound binding => .bound binding
  | .revealed binding publish => .finished (publication binding publish)

def representative : Code → ConfigCode
  | .initial => .initial
  | .bound binding => .bound binding
  | .finished result => .revealed result true

theorem code_representative (index : Code) : code (representative index) = index := by
  cases index <;> rfl

def active : ConfigCode → Bool
  | .initial | .bound _ => true
  | .revealed _ _ => false

def operator (label : ConfigCode × Action) : (ConfigCode → ℝ) →ₗ[ℝ] (ConfigCode → ℝ) :=
  if active label.1 then observedOperator id advance label else 0

def basis (index : Code) (state : ConfigCode) : ℝ := if code state = index then 1 else 0

def seed (outcome : Readout) (state : ConfigCode) : ℝ := if readout state = outcome then 1 else 0

def space : Submodule ℝ (ConfigCode → ℝ) := Submodule.span ℝ (Set.range basis)

open Classical in
/-- Every retained branch uses the real player observation; halted rows have no callback. -/
theorem operator_actual_observation (label : ConfigCode × Action) (value : ConfigCode → ℝ)
    (state : ConfigCode) :
    operator label value state =
      if active state then
        if observation state = observation label.1 then expect (advance state label.2) value
        else 0
      else 0 := by
  classical
  have observed : observation state = observation label.1 ↔ state = label.1 :=
    observation_injective.eq_iff
  by_cases current : active state = true <;>
    by_cases addressed : active label.1 = true <;>
    by_cases same : state = label.1 <;>
    simp_all [operator, observedOperator]

theorem basis_mem (index : Code) : basis index ∈ space :=
  Submodule.subset_span ⟨index, rfl⟩

theorem operator_basis (label : ConfigCode × Action) (index : Code) :
    operator label (basis index) =
      if active label.1 then
        (if code (next label.1 label.2) = index then (1 : ℝ) else 0) • basis (code label.1)
      else 0 := by
  classical
  cases label with
  | mk observed action =>
      cases observed with
      | initial =>
          funext state
          cases state <;> simp [operator, active, observedOperator, advance, next, basis, code,
            expect_pure]
      | bound binding =>
          funext state
          cases state <;> simp [operator, active, observedOperator, advance, next, basis, code,
            expect_pure]
          split_ifs <;> simp_all
      | revealed binding publish => simp [operator, active]

theorem closed (label : ConfigCode × Action) (value : ConfigCode → ℝ) (member : value ∈ space) :
    operator label value ∈ space := by
  apply map_mem_span (operator label) basis ?_ member
  intro index
  rw [operator_basis]
  split
  · exact space.smul_mem _ (basis_mem _)
  · exact space.zero_mem

def codeReadout : Code → Readout
  | .initial | .bound _ => .unfinished
  | .finished .failure => .failed
  | .finished (.success false) => .falsePublication
  | .finished (.success true) => .truePublication

theorem readout_code (state : ConfigCode) : codeReadout (code state) = readout state := by
  cases state with
  | initial => rfl
  | bound _ => rfl
  | revealed binding publish =>
      cases result : publication binding publish with
      | failure => simp [codeReadout, code, readout, result]
      | success bit => cases bit <;> simp [codeReadout, code, readout, result]

theorem seed_representation (outcome : Readout) :
    seed outcome = ∑ index : Code,
      (if codeReadout index = outcome then (1 : ℝ) else 0) • basis index := by
  classical
  funext state
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basis]
  simp [seed, ← readout_code]

theorem seed_mem (outcome : Readout) : seed outcome ∈ space := by
  rw [seed_representation]
  exact space.sum_mem fun index _ => space.smul_mem _ (basis_mem index)

theorem seed_sum : ∑ outcome : Readout, seed outcome = (fun _ : ConfigCode => (1 : ℝ)) := by
  classical
  funext state
  simp [seed]

theorem basis_independent : LinearIndependent ℝ basis := by
  classical
  apply linearIndependent_iff'.mpr
  intro indices coefficients zero index present
  have value := congrFun zero (representative index)
  simpa [basis, code_representative, Finset.sum_apply, present] using value

/-- Exact closure: three completed publication classes and four callback states. -/
theorem orbitSpan_eq_space : orbitSpan operator seed = space := by
  classical
  apply le_antisymm
  · exact orbitSpan_le operator seed space seed_mem closed
  · apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    have one : (fun _ : ConfigCode => (1 : ℝ)) ∈ orbitSpan operator seed := by
      rw [← seed_sum]
      exact (orbitSpan operator seed).sum_mem fun outcome _ =>
        seed_mem_orbitSpan operator seed outcome
    cases index with
    | initial =>
        have same : basis .initial = operator (.initial, (.failure, false)) (fun _ => 1) := by
          funext state
          cases state <;> simp [basis, code, operator, active, observedOperator, advance,
            expect_pure]
        rw [same]
        exact operator_mem_orbitSpan operator seed (.initial, (.failure, false)) one
    | bound binding =>
        have same : basis (.bound binding) =
            operator (.bound binding, (.failure, false)) (fun _ => 1) := by
          funext state
          cases state <;> simp [basis, code, operator, active, observedOperator, advance,
            expect_pure]
        rw [same]
        exact operator_mem_orbitSpan operator seed (.bound binding, (.failure, false)) one
    | finished result =>
        have resultCases : result = .failure ∨
            result = .success false ∨ result = .success true := by
          cases result with
          | failure => exact Or.inl rfl
          | success bit => cases bit <;> simp
        have same : basis (.finished result) = seed (codeReadout (.finished result)) := by
          rcases resultCases with rfl | rfl | rfl
          all_goals
            funext state
            cases state with
            | initial => simp [basis, code, seed, readout, codeReadout]
            | bound binding => simp [basis, code, seed, readout, codeReadout]
            | revealed binding publish =>
                cases actual : publication binding publish with
                | failure => simp [basis, code, seed, readout, codeReadout, actual]
                | success bit =>
                    cases bit <;> simp [basis, code, seed, readout, codeReadout, actual]
        rw [same]
        cases result with
        | failure => exact seed_mem_orbitSpan operator seed .failed
        | success bit =>
            cases bit
            · exact seed_mem_orbitSpan operator seed .falsePublication
            · exact seed_mem_orbitSpan operator seed .truePublication

theorem observable_dimension : Module.finrank ℝ (orbitSpan operator seed) = 7 := by
  rw [orbitSpan_eq_space]
  exact (finrank_span_eq_card basis_independent).trans (by decide)

/-- The checked certificate transports every callback-labelled selected continuation word. -/
theorem selected_word_eq (left right : ConfigCode) (same : code left = code right)
    (labels : List (ConfigCode × Action)) (outcome : Readout) :
    word operator labels (seed outcome) left = word operator labels (seed outcome) right := by
  have invariant : ∀ value ∈ space, value left = value right := by
    intro value member
    refine Submodule.span_induction ?_ ?_ ?_ ?_ member
    · rintro _ ⟨index, rfl⟩
      simp [basis, same]
    · rfl
    · intro first second _ _ firstEqual secondEqual
      change first left + second left = first right + second right
      rw [firstEqual, secondEqual]
    · intro scalar value _ equal
      change scalar * value left = scalar * value right
      rw [equal]
  exact invariant _ (word_mem operator space closed (seed_mem outcome) labels)

end Vegas.Examples.ProgramPaymentsObservableCertificate
