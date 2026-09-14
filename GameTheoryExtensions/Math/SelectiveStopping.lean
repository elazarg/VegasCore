/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Choosing whether to stop after observing a state

The state may contain a committed action and observations learned afterwards.
`true` selects stopping; `false` selects the feasible continuation with that
same state. Both branches may have further randomness. Comparisons are made at
the decision point, so an earlier comparison of unconditional expectations is
not a substitute for the hypotheses below.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {State Outcome : Type*}

/-- Some supported outcome attains at least the expectation of any real
observable under a finite distribution. -/
theorem exists_expect_le_support {α : Type*} (law : FinDist α) (value : α → ℝ) :
    ∃ a ∈ law.support, law.expect value ≤ value a := by
  by_contra h
  have hstrict : ∀ a ∈ law.support, value a < law.expect value := by
    intro a ha
    exact lt_of_not_ge (fun hle => h ⟨a, ha, hle⟩)
  obtain ⟨a, ha⟩ := law.support_nonempty
  exact (lt_irrefl _)
    (law.expect_lt_of_mem_support value (law.expect value)
      (fun b hb => (hstrict b hb).le) ha (hstrict a ha))

/-- Branchwise continuation superiority survives arbitrary informed,
randomized stopping. A uniform margin charges the probability of stopping.
The premise is needed only at supported states where stopping is possible. -/
theorem selective_stopping_bound
    (states : FinDist State) (stop : State → FinDist Bool)
    (quit proceed : State → FinDist Outcome) (utility : Outcome → ℝ) (margin : ℝ)
    (hmargin : ∀ state ∈ states.support, true ∈ (stop state).support →
      (quit state).expect utility + margin ≤ (proceed state).expect utility) :
    (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state).expect utility +
        margin * (states.bind stop).prob true ≤
      (states.bind proceed).expect utility := by
  simp only [expect_bind, prob_bind]
  rw [← expect_smul, ← expect_add]
  apply expect_mono
  intro state hstate
  rw [mul_comm margin, ← expect_ite_eq, ← expect_add]
  apply expect_le_of_forall
  intro stops hstops
  cases stops with
  | false => simp
  | true => simpa using hmargin state hstate hstops

/-- Weak continuation superiority suffices to remove the informed stopping
option when proving an upper bound on the decision maker's utility. -/
theorem selective_stopping_le
    (states : FinDist State) (stop : State → FinDist Bool)
    (quit proceed : State → FinDist Outcome) (utility : Outcome → ℝ)
    (hcontinue : ∀ state ∈ states.support, true ∈ (stop state).support →
      (quit state).expect utility ≤ (proceed state).expect utility) :
    (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state).expect utility ≤
      (states.bind proceed).expect utility := by
  simpa using selective_stopping_bound states stop quit proceed utility 0
    (fun state hstate hstop => by simpa using hcontinue state hstate hstop)

/-- A positive margin makes any positive probability of stopping strictly
worse than feasible continuation. Unreached stopping decisions are unrestricted. -/
theorem selective_stopping_lt
    (states : FinDist State) (stop : State → FinDist Bool)
    (quit proceed : State → FinDist Outcome) (utility : Outcome → ℝ) (margin : ℝ)
    (hmargin : ∀ state ∈ states.support, true ∈ (stop state).support →
      (quit state).expect utility + margin ≤ (proceed state).expect utility)
    (hpositive : 0 < margin) (hstops : 0 < (states.bind stop).prob true) :
    (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state).expect utility <
      (states.bind proceed).expect utility := by
  have hbound := selective_stopping_bound states stop quit proceed utility margin hmargin
  have hcost := mul_pos hpositive hstops
  linarith

/-- Fiberwise utility comparison at the information available when stopping
implies an unconditional comparison. The fiber hypotheses use unnormalized
expectations, so zero-probability information values require no conditioning
or division. Outside the stopping event, a pointwise weak comparison suffices. -/
theorem stopping_information_fiber_bound {Information : Type*}
    [DecidableEq Information]
    (law : FinDist State) (stopped : State → Bool)
    (information : State → Information)
    (sourceValue targetValue : State → ℝ) (margin : ℝ)
    (houtside : ∀ state ∈ law.support, stopped state = false →
      targetValue state ≤ sourceValue state)
    (hfiber : ∀ observed,
      (∃ state ∈ law.support, stopped state = true ∧ information state = observed) →
      law.expect (fun state =>
          if stopped state && decide (information state = observed)
          then targetValue state + margin else 0) ≤
        law.expect (fun state =>
          if stopped state && decide (information state = observed)
          then sourceValue state else 0)) :
    law.expect targetValue + margin * (law.map stopped).prob true ≤
      law.expect sourceValue := by
  classical
  let fibers : Finset Information :=
    (law.supportFinset.filter fun state => stopped state = true).image information
  have hfibers :
      (∑ observed : ↑fibers, law.expect (fun state =>
          if stopped state && decide (information state = observed.1)
          then targetValue state + margin else 0)) ≤
        ∑ observed : ↑fibers, law.expect (fun state =>
          if stopped state && decide (information state = observed.1)
          then sourceValue state else 0) := by
    apply Finset.sum_le_sum
    intro observed _
    apply hfiber observed.1
    obtain ⟨state, hstate, hinfo⟩ := Finset.mem_image.mp observed.2
    obtain ⟨hsupport, hstopped⟩ := Finset.mem_filter.mp hstate
    exact ⟨state, mem_supportFinset.mp hsupport, hstopped, hinfo⟩
  rw [expect_sum_comm, expect_sum_comm] at hfibers
  have htargetFibers :
      law.expect (fun state => ∑ observed : ↑fibers,
          if stopped state && decide (information state = observed.1)
          then targetValue state + margin else 0) =
        law.expect (fun state =>
          if stopped state then targetValue state + margin else 0) := by
    apply expect_congr
    intro state hstate
    cases hstopped : stopped state with
    | false => simp
    | true =>
        have hmem : information state ∈ fibers := by
          apply Finset.mem_image.mpr
          exact ⟨state, Finset.mem_filter.mpr
            ⟨mem_supportFinset.mpr hstate, hstopped⟩, rfl⟩
        simp only [Bool.true_and, decide_eq_true_eq, ↓reduceIte]
        change (∑ observed ∈ fibers.attach,
          if information state = observed.1 then targetValue state + margin else 0) = _
        rw [Finset.sum_eq_single ⟨information state, hmem⟩
          (fun observed _ hne => by
            have hvalue : information state ≠ observed.1 := by
              intro heq
              apply hne
              apply Subtype.ext
              exact heq.symm
            simp [hvalue])
          (fun hnot => absurd (Finset.mem_attach _ _) hnot)]
        simp
  have hsourceFibers :
      law.expect (fun state => ∑ observed : ↑fibers,
          if stopped state && decide (information state = observed.1)
          then sourceValue state else 0) =
        law.expect (fun state => if stopped state then sourceValue state else 0) := by
    apply expect_congr
    intro state hstate
    cases hstopped : stopped state with
    | false => simp
    | true =>
        have hmem : information state ∈ fibers := by
          apply Finset.mem_image.mpr
          exact ⟨state, Finset.mem_filter.mpr
            ⟨mem_supportFinset.mpr hstate, hstopped⟩, rfl⟩
        simp only [Bool.true_and, decide_eq_true_eq, ↓reduceIte]
        change (∑ observed ∈ fibers.attach,
          if information state = observed.1 then sourceValue state else 0) = _
        rw [Finset.sum_eq_single ⟨information state, hmem⟩
          (fun observed _ hne => by
            have hvalue : information state ≠ observed.1 := by
              intro heq
              apply hne
              apply Subtype.ext
              exact heq.symm
            simp [hvalue])
          (fun hnot => absurd (Finset.mem_attach _ _) hnot)]
        simp
  rw [htargetFibers, hsourceFibers] at hfibers
  rw [prob_map, ← expect_smul, ← expect_add]
  calc
    law.expect (fun state =>
        targetValue state + margin * (if true = stopped state then 1 else 0)) =
        law.expect (fun state => if stopped state then targetValue state + margin else 0) +
          law.expect (fun state => if stopped state then 0 else targetValue state) := by
      rw [← expect_add]
      apply expect_congr
      intro state _
      cases stopped state <;> simp
    _ ≤ law.expect (fun state => if stopped state then sourceValue state else 0) +
        law.expect (fun state => if stopped state then 0 else sourceValue state) := by
      apply add_le_add hfibers
      apply expect_mono
      intro state hstate
      cases hstopped : stopped state with
      | false => simpa using houtside state hstate hstopped
      | true => simp
    _ = law.expect sourceValue := by
      rw [← expect_add]
      apply expect_congr
      intro state _
      cases stopped state <;> simp

/-- The best fully informed stopping policy attains the pointwise maximum of
the two continuation expectations. This identifies the exact value of the
extra decision, without assuming a particular source information model. -/
theorem selective_stopping_optimal
    (states : FinDist State) (quit proceed : State → FinDist Outcome)
    (utility : Outcome → ℝ) :
    ∃ stop : State → FinDist Bool,
      (states.bind fun state => (stop state).bind fun stops =>
          if stops then quit state else proceed state).expect utility =
        states.expect (fun state => max ((quit state).expect utility)
          ((proceed state).expect utility)) ∧
      ∀ alternative : State → FinDist Bool,
        (states.bind fun state => (alternative state).bind fun stops =>
            if stops then quit state else proceed state).expect utility ≤
          states.expect (fun state => max ((quit state).expect utility)
            ((proceed state).expect utility)) := by
  classical
  refine ⟨fun state => pure (decide ((proceed state).expect utility ≤
    (quit state).expect utility)), ?_, ?_⟩
  · simp only [expect_bind, pure_bind]
    apply expect_congr
    intro state _
    by_cases h : (proceed state).expect utility ≤ (quit state).expect utility
    · simp [h]
    · simp [h, max_eq_right (le_of_lt (lt_of_not_ge h))]
  · intro alternative
    simp only [expect_bind]
    apply expect_mono
    intro state _
    apply expect_le_of_forall
    intro stops _
    cases stops
    · exact le_max_right _ _
    · exact le_max_left _ _

/-- Across all state laws and informed policies, eliminating stopping is valid
exactly when continuation is at least as good at every decision state. -/
theorem selective_stopping_le_iff
    (quit proceed : State → FinDist Outcome) (utility : Outcome → ℝ) :
    (∀ (states : FinDist State) (stop : State → FinDist Bool),
      (states.bind fun state => (stop state).bind fun stops =>
          if stops then quit state else proceed state).expect utility ≤
        (states.bind proceed).expect utility) ↔
      ∀ state, (quit state).expect utility ≤ (proceed state).expect utility := by
  constructor
  · intro hall state
    simpa using hall (pure state) (fun _ => pure true)
  · intro hall states stop
    exact selective_stopping_le states stop quit proceed utility (fun state _ _ => hall state)

end GameTheory.Math.Probability.FinDist

/-- info: 'GameTheory.Math.Probability.FinDist.selective_stopping_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.FinDist.selective_stopping_bound

/-- info: 'GameTheory.Math.Probability.FinDist.stopping_information_fiber_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.FinDist.stopping_information_fiber_bound

/-- info: 'GameTheory.Math.Probability.FinDist.selective_stopping_optimal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.FinDist.selective_stopping_optimal

/-- info: 'GameTheory.Math.Probability.FinDist.selective_stopping_le_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.FinDist.selective_stopping_le_iff
