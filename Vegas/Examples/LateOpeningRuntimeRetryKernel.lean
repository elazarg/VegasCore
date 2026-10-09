/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLatePrefixKernel
import Vegas.Examples.LateOpeningRuntimeAliceTremble
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Physical final-response errors at actual pending-opening decisions

The original decoded response law is followed by the existing lottery, clock,
expiry and receiver activation. Its distance from the silent-response branch
is bounded by the actual native information site's probability of sending an
additional packet. This estimate applies to every event of the full execution
law, including receiver information and initialized-type readouts.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeRetryKernel

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeAliceDecision LateOpeningRuntimeLatePrefixKernel

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def responseLaw (decision : DecisionHistory weight nonnegative)
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    PMF app.Execution :=
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile
  (players alice (decision.execution.recall alice) (decision.execution.observe app alice)).bind
    fun response => settlementKernel weight nonnegative
      (decision.execution.respond app alice response)

def quietLaw (decision : DecisionHistory weight nonnegative) : PMF app.Execution :=
  settlementKernel weight nonnegative (decision.execution.respond app alice ⟨none⟩)

/-- This is the actual original final callback and its subsequent physical
service, with no change to the source or target response alphabet. -/
theorem response_law_physical (decision : DecisionHistory weight nonnegative)
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) profile
    ((app.invoke players alice decision.execution).bind fun responded =>
      (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 3
        responded).bind fun before => before.environmentStep app (.activate bob)) =
      responseLaw weight nonnegative decision profile := by
  dsimp only
  unfold ReactiveApplication.invoke responseLaw
  rw [PMF.bind_map]
  apply bind_congr_on_support
  intro response _
  simp only [Function.comp_apply]
  exact settlement_activation weight nonnegative _ _
    (by rw [app.respond_environmentRecall, decision_cursor weight nonnegative decision])

private theorem emission_probability_eq_complement (law : PMF app.Action) :
    (law.toOuterMeasure {response | response.transmission.isSome}).toReal =
      1 - (law (⟨none⟩ : app.Action)).toReal := by
  classical
  rw [← expect_indicator]
  have indicator : (fun response : app.Action =>
      @ite ℝ (response ∈ {action : app.Action | action.transmission.isSome})
        (Classical.propDecidable _) 1 0) =
        fun response => 1 - if (⟨none⟩ : app.Action) = response then 1 else 0 := by
    funext response
    rcases response with ⟨transmission⟩
    cases transmission <;> simp
  rw [indicator, expect_sub (payoffIntegrable_constant law 1)
    (payoffIntegrable_of_bounded law _ (C := 1) fun response => by
      split_ifs <;> norm_num), expect_constant, expect_ite_eq, mul_one]

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨18, some alice, decision.execution⟩)

include current in
/-- Every actual information event differs from the quiet physical branch by
at most the native site's own additional-packet probability. -/
theorem response_close_quiet
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    PMF.WithinTV (LateOpeningRuntimeAliceTremble.emissionProbability
      weight nonnegative profile site) (responseLaw weight nonnegative decision profile)
        (quietLaw weight nonnegative decision) := by
  have information := representative.2
  change (rawMenu.signals initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)).infoOf alice
      representative.1.trace = site.1 at information
  rw [rawMenu.info, current] at information
  have observed : site.1 = some (decision.execution.recall alice,
      decision.execution.observe app alice) := by
    simpa only [ReactiveApplication.observe, ↓reduceIte] using information.symm
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile
  let responses := players alice (decision.execution.recall alice)
    (decision.execution.observe app alice)
  have emission : LateOpeningRuntimeAliceTremble.emissionProbability
      weight nonnegative profile site =
        (responses.toOuterMeasure {response | response.transmission.isSome}).toReal := by
    rw [LateOpeningRuntimeAliceTremble.emissionProbability, observed]
    simp only [responses, players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      PMF.map_comp]
    rfl
  exact PMF.WithinTV.of_bind_point responses (⟨none⟩ : app.Action)
    (fun response => settlementKernel weight nonnegative
      (decision.execution.respond app alice response))
    (by rw [emission, emission_probability_eq_complement])

/-- Arbitrary nonnegative prefix weights keep the exact relative native
retry bound. In particular their sum need not have a positive limiting value. -/
theorem weighted_event_error_bound {Root : Type} [Fintype Root]
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (sites : Root → (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (histories : ∀ root, (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice (sites root).1)
    (decisions : Root → DecisionHistory weight nonnegative)
    (atDecision : ∀ root, (histories root).1.state =
      some ⟨18, some alice, (decisions root).execution⟩)
    (prefixWeight : Root → ℝ) (prefixNonnegative : ∀ root, 0 ≤ prefixWeight root)
    (event : Set app.Execution) (error : ℝ)
    (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative profile actual.1 ≤ error) :
    |∑ root, prefixWeight root *
      (((responseLaw weight nonnegative (decisions root) profile).toOuterMeasure event).toReal -
        ((quietLaw weight nonnegative (decisions root)).toOuterMeasure event).toReal)| ≤
      error * ∑ root, prefixWeight root := by
  have pointwise root := response_close_quiet weight nonnegative (sites root)
    (histories root) (decisions root) (atDecision root) profile event
  calc
    _ ≤ ∑ root, |prefixWeight root *
        (((responseLaw weight nonnegative (decisions root) profile).toOuterMeasure event).toReal -
          ((quietLaw weight nonnegative (decisions root)).toOuterMeasure event).toReal)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ root, prefixWeight root *
        LateOpeningRuntimeAliceTremble.emissionProbability
          weight nonnegative profile (sites root) := by
      apply Finset.sum_le_sum
      intro root _
      rw [abs_mul, abs_of_nonneg (prefixNonnegative root)]
      exact mul_le_mul_of_nonneg_left (pointwise root) (prefixNonnegative root)
    _ ≤ _ := LateOpeningRuntimeAliceTremble.weighted_retry_bound weight nonnegative profile
      (fun root => ⟨sites root, decisions root, histories root, atDecision root⟩)
      prefixWeight prefixNonnegative error
        (fun root => bound ⟨sites root, decisions root, histories root, atDecision root⟩)

/-- The relative error vanishes for the same actual sequence and uniform
native retry bound, even when the original prefix weights vanish faster. -/
theorem relative_event_error_tendsto {Root : Type} [Fintype Root]
    (sequence : ℕ → ∀ who,
      (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (sites : ℕ → Root →
      (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (histories : ∀ n root,
      (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice (sites n root).1)
    (decisions : ℕ → Root → DecisionHistory weight nonnegative)
    (atDecision : ∀ n root, (histories n root).1.state =
      some ⟨18, some alice, (decisions n root).execution⟩)
    (prefixWeight : ℕ → Root → ℝ)
    (prefixNonnegative : ∀ n root, 0 ≤ prefixWeight n root)
    (prefixPositive : ∀ n, 0 < ∑ root, prefixWeight n root)
    (event : ℕ → Set app.Execution) (error : ℕ → ℝ)
    (vanishes : Filter.Tendsto error Filter.atTop (nhds 0))
    (bound : ∀ n
      (actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative),
      LateOpeningRuntimeAliceTremble.emissionProbability
        weight nonnegative (sequence n) actual.1 ≤ error n) :
    Filter.Tendsto (fun n =>
      |∑ root, prefixWeight n root *
        (((responseLaw weight nonnegative (decisions n root) (sequence n)).toOuterMeasure
          (event n)).toReal - ((quietLaw weight nonnegative (decisions n root)).toOuterMeasure
            (event n)).toReal)| / (∑ root, prefixWeight n root)) Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (abs_nonneg _) (prefixPositive n).le
  · intro n
    apply (div_le_iff₀ (prefixPositive n)).mpr
    exact weighted_event_error_bound weight nonnegative (sequence n) (sites n) (histories n)
      (decisions n) (atDecision n) (prefixWeight n) (prefixNonnegative n) (event n) (error n)
        (bound n)
  · exact vanishes

end Vegas.Examples.LateOpeningRuntimeRetryKernel
