/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.PrivateObservableTransport
import GameTheory.Math.Probability.ExpectationConditioning

/-! # Actual adaptive transcript masses from labelled observation operators

The policy's probability of a fixed complete input/output transcript factors
from its unnormalized hidden-state moment. The coefficient uses the player's
actual remembered transcript at every choice. No blind-policy premise is used.
-/

noncomputable section

namespace GameTheory.Protocol.PrivateStrategy

open GameTheory.Math.Probability GameTheory.Math.InvariantObservables

variable {State Input Output : Type*} [Finite State]

/-- The probability of the specified responses along one observable word.
It depends on the policy and transcript, not on the hidden environment state. -/
def transcriptFactor (policy : Transcript Input Output → Input → PMF Output) :
    List (Input × Output) → Transcript Input Output → ℝ
  | [], _ => 1
  | label :: rest, past => (policy past label.1 label.2).toReal *
      transcriptFactor policy rest (label :: past)

open Classical in
/-- A selected transcript's unnormalized terminal score in the actual runner. -/
def transcriptScore (observed : Transcript Input Output) (value : State → ℝ)
    (result : State × Transcript Input Output) : ℝ :=
  if result.2 = observed then value result.1 else 0

omit [Finite State] in
theorem runBehavioral_past
    (policy : Transcript Input Output → Input → PMF Output)
    (observe : State → Input) (advance : State → Output → PMF State)
    (count : Nat) (past : Transcript Input Output) (state : State)
    (result : State × Transcript Input Output)
    (supported : result ∈ (runBehavioral policy observe advance count past state).support) :
    result.2.drop count = past := by
  induction count generalizing past state with
  | zero =>
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst result
      rfl
  | succ count ih =>
      simp only [runBehavioral, PMF.support_bind, Set.mem_iUnion] at supported
      obtain ⟨output, _, next, _, reached⟩ := supported
      have prior := ih ((observe state, output) :: past) next reached
      simpa only [List.drop_drop, Nat.add_comm, List.drop_succ_cons, List.drop_zero] using
        congrArg (List.drop 1) prior

private theorem transcriptScore_bounded (observed : Transcript Input Output)
    (value : State → ℝ) : ∃ bound, ∀ result, |transcriptScore observed value result| ≤ bound := by
  classical
  obtain ⟨bound, above⟩ := (Set.finite_range fun state => |value state|).bddAbove
  refine ⟨max bound 0, fun result => ?_⟩
  unfold transcriptScore
  split
  · exact (above ⟨result.1, rfl⟩).trans (le_max_left _ _)
  · simpa only [abs_zero] using le_max_right bound 0

omit [Finite State] in
/-- The canonical runner cannot replace any part of an already remembered
transcript. A word attached to a different past therefore has zero mass. -/
theorem expect_transcriptScore_of_ne_past
    (policy : Transcript Input Output → Input → PMF Output)
    (observe : State → Input) (advance : State → Output → PMF State)
    (labels : List (Input × Output)) (first second : Transcript Input Output)
    (different : first ≠ second) (state : State) (value : State → ℝ) :
    expect (runBehavioral policy observe advance labels.length first state)
      (transcriptScore (labels.reverse ++ second) value) = 0 := by
  classical
  apply (expect_congr_on_support (f := transcriptScore (labels.reverse ++ second) value)
    (g := fun _ => 0) ?_).trans (expect_zero _)
  intro result reached
  have remembered := runBehavioral_past policy observe advance labels.length first state
    result reached
  unfold transcriptScore
  split
  · next same =>
    rw [same] at remembered
    have equal : second = first := by simpa using remembered
    exact (different equal.symm).elim
  · rfl

/-- The actual adaptive runner's selected transcript moment factors into the
policy's response weights and the observation-filtered kernel word. -/
theorem expect_runBehavioral_transcriptScore
    (policy : Transcript Input Output → Input → PMF Output)
    (observe : State → Input) (advance : State → Output → PMF State)
    (labels : List (Input × Output)) (past : Transcript Input Output)
    (state : State) (value : State → ℝ) :
    expect (runBehavioral policy observe advance labels.length past state)
        (transcriptScore (labels.reverse ++ past) value) =
      transcriptFactor policy labels past * word (observedOperator observe advance) labels value
        state := by
  classical
  induction labels generalizing past state with
  | nil => simp [runBehavioral, expect_pure, transcriptScore, transcriptFactor]
  | cons label rest ih =>
      rcases label with ⟨input, chosen⟩
      let selected := transcriptScore (rest.reverse ++ (input, chosen) :: past) value
      obtain ⟨bound, bounded⟩ := transcriptScore_bounded (rest.reverse ++ (input, chosen) :: past)
        value
      have expansion :
          expect (runBehavioral policy observe advance (rest.length + 1) past state) selected =
          expect (policy past (observe state)) (fun output =>
            expect (advance state output) (fun next =>
              expect (runBehavioral policy observe advance rest.length
                ((observe state, output) :: past) next) selected)) := by
        rw [runBehavioral, expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)]
        apply expect_congr_on_support
        intro output _
        exact expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)
      have branch (output : Output) :
          expect (advance state output) (fun next =>
            expect (runBehavioral policy observe advance rest.length
              ((observe state, output) :: past) next) selected) =
          if observe state = input ∧ output = chosen then
            transcriptFactor policy rest ((input, chosen) :: past) *
              expect (advance state chosen) (word (observedOperator observe advance) rest value)
          else 0 := by
        by_cases same : observe state = input ∧ output = chosen
        · rw [ite_eq_left same]
          rcases same with ⟨observed, rfl⟩
          simp only [observed]
          simp only [selected, ih, expect_const_mul]
        · rw [ite_eq_right same]
          have different : ((observe state, output) :: past) ≠ (input, chosen) :: past := by
            intro equal
            have pair := (List.cons.inj equal).1
            exact same ⟨congrArg Prod.fst pair, congrArg Prod.snd pair⟩
          have zero : ∀ next,
              expect (runBehavioral policy observe advance rest.length
                ((observe state, output) :: past) next) selected = 0 :=
            fun next => expect_transcriptScore_of_ne_past policy observe advance rest _ _
              different next value
          simp only [zero, expect_zero]
      simp only [List.length_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
      change expect (runBehavioral policy observe advance (rest.length + 1) past state)
        selected = _
      rw [expansion]
      simp_rw [branch]
      by_cases observed : observe state = input
      · simp only [observed, true_and]
        have single := expect_ite_eq (policy past input) chosen
          (transcriptFactor policy rest ((input, chosen) :: past) *
            expect (advance state chosen) (word (observedOperator observe advance) rest value))
        have flip :
            (fun output : Output => if output = chosen then
                transcriptFactor policy rest ((input, chosen) :: past) *
                  expect (advance state chosen)
                    (word (observedOperator observe advance) rest value) else 0) =
              (fun output => if chosen = output then
                transcriptFactor policy rest ((input, chosen) :: past) *
                  expect (advance state chosen)
                    (word (observedOperator observe advance) rest value) else 0) := by
          funext output
          simp only [eq_comm]
        rw [flip, single]
        simp only [transcriptFactor, word_cons, observedOperator, LinearMap.coe_mk,
          AddHom.coe_mk, observed, ↓reduceIte]
        ring
      · simp only [observed, false_and, ↓reduceIte, expect_zero]
        simp [transcriptFactor, observedOperator, observed]

/-- Mixing the actual initial hidden state preserves the same observable
policy factor, because the policy does not read that hidden state. -/
theorem expect_initial_runBehavioral_transcriptScore
    (prior : PMF State) (policy : Transcript Input Output → Input → PMF Output)
    (observe : State → Input) (advance : State → Output → PMF State)
    (labels : List (Input × Output)) (past : Transcript Input Output) (value : State → ℝ) :
    expect (prior.bind (runBehavioral policy observe advance labels.length past))
        (transcriptScore (labels.reverse ++ past) value) =
      transcriptFactor policy labels past *
        expect prior (word (observedOperator observe advance) labels value) := by
  obtain ⟨bound, bounded⟩ := transcriptScore_bounded (labels.reverse ++ past) value
  rw [expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ bounded)]
  simp only [expect_runBehavioral_transcriptScore, expect_const_mul]

omit [Finite State] in
theorem transcriptFactor_nonnegative
    (policy : Transcript Input Output → Input → PMF Output)
    (labels : List (Input × Output)) (past : Transcript Input Output) :
    0 ≤ transcriptFactor policy labels past := by
  induction labels generalizing past with
  | nil => exact zero_le_one
  | cons label rest ih => exact mul_nonneg ENNReal.toReal_nonneg (ih _)

omit [Finite State] in
/-- The selected transcript's unit score is its actual observation probability. -/
theorem expect_transcriptScore_one
    (law : PMF (State × Transcript Input Output)) (observed : Transcript Input Output) :
    expect law (transcriptScore observed (fun _ => 1)) = ((law.map Prod.snd) observed).toReal := by
  classical
  rw [toReal_map_apply]
  apply expect_congr_on_support
  intro result _
  simp [transcriptScore, eq_comm]

/-- A supported actual transcript has positive policy weight and positive
unnormalized kernel mass. Null fibers cannot satisfy either conclusion. -/
theorem supported_transcript_factors_positive
    (prior : PMF State) (policy : Transcript Input Output → Input → PMF Output)
    (observe : State → Input) (advance : State → Output → PMF State)
    (labels : List (Input × Output)) (past : Transcript Input Output)
    (supported : labels.reverse ++ past ∈ (PMF.map Prod.snd
      (prior.bind (runBehavioral policy observe advance labels.length past))).support) :
    0 < transcriptFactor policy labels past ∧
      0 < expect prior (word (observedOperator observe advance) labels (fun _ => 1)) := by
  have positive : 0 < ((PMF.map Prod.snd
      (prior.bind (runBehavioral policy observe advance labels.length past)))
        (labels.reverse ++ past)).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp supported) (PMF.apply_ne_top _ _)
  rw [← expect_transcriptScore_one, expect_initial_runBehavioral_transcriptScore] at positive
  rcases mul_pos_iff.mp positive with both | negative
  · exact both
  · exact (not_lt_of_ge (transcriptFactor_nonnegative policy labels past) negative.1).elim

/-- The actual positive-probability transcript posterior has the normalized
operator-word expectation. All adaptive policy factors cancel exactly. -/
theorem expect_posterior_runBehavioral_transcript
    (prior : PMF State) (policy : Transcript Input Output → Input → PMF Output)
    (observe : State → Input) (advance : State → Output → PMF State)
    (labels : List (Input × Output)) (past : Transcript Input Output) (value : State → ℝ)
    (supported : labels.reverse ++ past ∈ (PMF.map Prod.snd
      (prior.bind (runBehavioral policy observe advance labels.length past))).support) :
    expect (fiberPosterior
        (prior.bind (runBehavioral policy observe advance labels.length past))
        Prod.snd (labels.reverse ++ past)) (fun result => value result.1) =
      expect prior (word (observedOperator observe advance) labels value) /
        expect prior (word (observedOperator observe advance) labels (fun _ => 1)) := by
  classical
  let law := prior.bind (runBehavioral policy observe advance labels.length past)
  let observed := labels.reverse ++ past
  have marginal :
      (∑' result, (Prod.snd ⁻¹' {observed}).indicator law result) =
        (law.map Prod.snd) observed := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro result
    simp [Set.indicator, eq_comm]
  have numerator : (Prod.snd ⁻¹' {observed}).indicator (fun result : State ×
      Transcript Input Output => value result.1) = transcriptScore observed value := by
    funext result
    simp [Set.indicator, transcriptScore]
  have mass : ((law.map Prod.snd) observed).toReal =
      transcriptFactor policy labels past *
      expect prior (word (observedOperator observe advance) labels (fun _ => 1)) := by
    rw [← expect_transcriptScore_one]
    exact expect_initial_runBehavioral_transcriptScore prior policy observe advance labels past _
  have factorPositive := (supported_transcript_factors_positive prior policy observe advance
    labels past supported).1
  change expect (fiberPosterior law Prod.snd observed) (fun result => value result.1) = _
  rw [expect_fiberPosterior law Prod.snd _ observed supported, numerator, marginal, mass,
    expect_initial_runBehavioral_transcriptScore]
  exact mul_div_mul_left _ _ factorPositive.ne'

end GameTheory.Protocol.PrivateStrategy
