/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSilentChoicePosterior

/-! # Resolution silence and the relative rate of source trembles

For two timing slots, the actual posterior after one first-turn silence puts
weight `w / (s * (1 - w) + w)` on the remaining slot. Here `s` is the actual
first canonical opportunity's silent likelihood. The next response's expected
reward for transmitting is that weight times its canonical transmission reward.
The reward is an action-level payoff test: transmitting earns one and silence
earns zero. Realizing it as a protected two-turn runtime's actual terminal
audited utility requires a separate completion and settlement bridge.

When both opportunities have source false mass `s`, this reward's expectation
is `(1 - s) * w / (s * (1 - w) + w)`. It vanishes if deferral is faster than
the false tremble, producing regret tending to one against a transmitting
response in this payoff test. The opposite relative rate makes that regret
vanish. These local calculations do not fix closed resolution gates, prove
source-view stability, or assert a native equilibrium counterexample.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- An action reward for the two-opportunity resolution test. Its realization
as actual runtime terminal audited utility is a separate obligation. -/
def resolutionTransmissionReward (response : (application setup leaks).Action) : ℝ :=
  if response.transmission = none then 0 else 1

private theorem transmissionReward_expect
    (law : PMF (application setup leaks).Action) :
    expect law resolutionTransmissionReward = 1 - (law ⟨none⟩).toReal := by
  classical
  have indicatorIntegrable : PayoffIntegrable law
      (fun response => if (⟨none⟩ : (application setup leaks).Action) = response then
        (1 : ℝ) else 0) := by
    apply payoffIntegrable_of_bounded law _ (C := 1)
    intro response
    split <;> norm_num
  calc
    _ = expect law (fun response => (1 : ℝ) -
        (if (⟨none⟩ : (application setup leaks).Action) = response then 1 else 0)) := by
      apply expect_congr_on_support
      intro response _
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => simp only [resolutionTransmissionReward, ↓reduceIte, sub_self]
      | some material =>
          have different : (⟨none⟩ : (application setup leaks).Action) ≠ ⟨some material⟩ := by
            intro equal
            cases congrArg ReactiveApplication.Action.transmission equal
          simp only [resolutionTransmissionReward, reduceCtorEq, different, ↓reduceIte, sub_zero]
    _ = _ := by
      rw [expect_sub (payoffIntegrable_constant law 1) indicatorIntegrable,
        expect_constant, expect_ite_eq, mul_one]

/-- The actual two-slot response law after a real first silence, derived from
the policy mixture's recall posterior. The next input is explicitly supplied;
neither another activation nor its deadline protection is inferred. -/
theorem sourceServiceTurnPolicy_first_silence_two_slots_response
    {bound : (graph setup).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {event : (graph setup).EventId}
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks who event (middle.recall who)
      (middle.observe (application setup leaks) who) = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal)
    (owned : (graph setup).actor? event = some who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1)
    (view : (application setup leaks).PlayerView)
    (next : sourceServiceTurn setup leaks who event
      ((middle.respond (application setup leaks) who ⟨none⟩).recall who) view = some 1)
    (response : (application setup leaks).Action) :
    let app := application setup leaks
    let past := (middle.respond app who ⟨none⟩).recall who
    let silent := ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      (middle.recall who) (middle.observe app who)) ⟨none⟩).toReal
    let hazard := weight / (silent * (1 - weight) + weight)
    ((sourceServiceTurnPolicy setup leaks bound 1
      (geometricTiming setup 1 weight nonnegative bounded) profile who past view)
        response).toReal =
      hazard * ((sourceServiceCanonicalOpportunity setup leaks bound profile who event past view)
        response).toReal + (1 - hazard) * ((PMF.pure ⟨none⟩) response).toReal := by
  dsimp only
  let app := application setup leaks
  let past := (middle.respond app who ⟨none⟩).recall who
  let timing := geometricTurnLaw weight nonnegative bounded 1
  let current : Fin (1 + 1) := 1
  let silent := ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
    (middle.recall who) (middle.observe app who)) ⟨none⟩).toReal
  have posterior := sourceServiceTurnFamily_first_silence_posterior timing middle first
    positive current
  have hazard : (((app.policyMixture timing
      (sourceServiceTurnFamily setup leaks bound profile who event 1)).posterior past)
        current).toReal = weight / (silent * (1 - weight) + weight) := by
    rw [posterior]
    simp only [timing, current, Fin.val_one, lt_self_iff_false, ↓reduceIte, mul_one,
      geometricTurnLaw_apply_toReal, Fin.val_zero, Nat.zero_lt_succ, pow_zero, pow_one]
    congr 1
    ring
  have serving : view.application.publicView.ownTurn? who = some event := by
    unfold sourceServiceTurn at next
    split at next
    · assumption
    · cases next
  rw [sourceServiceTurnPolicy_turn setup leaks bound 1 _ profile who _ view event owned serving]
  change (((app.policyMixture timing
    (sourceServiceTurnFamily setup leaks bound profile who event 1)).policy past view)
      response).toReal = _
  rw [sourceServiceTurnFamily_response_probability timing current past view next response,
    hazard]
  rfl

/-- The expected transmission reward under the actual continuation.
The first and next canonical silent masses are kept distinct, so no source-view
stability or later inclusion protection is assumed implicitly. -/
theorem sourceServiceTurnPolicy_first_silence_two_slots_reward
    {bound : (graph setup).EventId → Nat} {profile : BehavioralProfile setup.program}
    {who : Player} {event : (graph setup).EventId}
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks who event (middle.recall who)
      (middle.observe (application setup leaks) who) = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal)
    (owned : (graph setup).actor? event = some who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1)
    (view : (application setup leaks).PlayerView)
    (next : sourceServiceTurn setup leaks who event
      ((middle.respond (application setup leaks) who ⟨none⟩).recall who) view = some 1) :
    let app := application setup leaks
    let past := (middle.respond app who ⟨none⟩).recall who
    let silent := ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      (middle.recall who) (middle.observe app who)) ⟨none⟩).toReal
    expect (sourceServiceTurnPolicy setup leaks bound 1
      (geometricTiming setup 1 weight nonnegative bounded) profile who past view)
        resolutionTransmissionReward =
      (weight / (silent * (1 - weight) + weight)) *
        (1 - ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
          past view) ⟨none⟩).toReal) := by
  dsimp only
  rw [transmissionReward_expect,
    sourceServiceTurnPolicy_first_silence_two_slots_response middle first positive owned weight
      nonnegative bounded view next ⟨none⟩]
  simp only [PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
  ring

/-- Transmission probability when both turns have the same source false mass.
This is a numerical kernel, not a source-stability or terminal-utility axiom. -/
def twoSlotResolutionOpeningProbability (silent weight : ℝ) : ℝ :=
  (1 - silent) * weight / (silent * (1 - weight) + weight)

theorem twoSlotResolutionOpeningProbability_bounds {silent weight : ℝ}
    (positive : 0 < silent) (silentBound : silent ≤ 1)
    (nonnegative : 0 ≤ weight) :
    0 ≤ twoSlotResolutionOpeningProbability silent weight ∧
      twoSlotResolutionOpeningProbability silent weight ≤ weight / silent := by
  have lower : silent ≤ silent * (1 - weight) + weight := by nlinarith
  have denominator : 0 < silent * (1 - weight) + weight := lt_of_lt_of_le positive lower
  unfold twoSlotResolutionOpeningProbability
  constructor
  · exact div_nonneg (mul_nonneg (sub_nonneg.mpr silentBound) nonnegative) denominator.le
  · have numerator : (1 - silent) * weight ≤ weight := by nlinarith
    exact (div_le_div_of_nonneg_right numerator denominator.le).trans
      (div_le_div_of_nonneg_left nonnegative positive lower)

/-- Faster deferral makes the two-turn payoff test fail to transmit. Against a
sure transmitting response worth one, its action payoff regret tends to one. -/
theorem twoSlotResolutionOpeningProbability_fast_regret
    (silent weight : ℕ → ℝ) (positive : ∀ n, 0 < silent n)
    (silentBound : ∀ n, silent n ≤ 1) (nonnegative : ∀ n, 0 ≤ weight n)
    (relative : Tendsto (fun n => weight n / silent n) atTop (nhds 0)) :
    Tendsto (fun n => 1 - twoSlotResolutionOpeningProbability (silent n) (weight n))
      atTop (nhds 1) := by
  have vanishes : Tendsto (fun n => twoSlotResolutionOpeningProbability (silent n) (weight n))
      atTop (nhds 0) := squeeze_zero
    (fun n => (twoSlotResolutionOpeningProbability_bounds (positive n) (silentBound n)
      (nonnegative n)).1)
    (fun n => (twoSlotResolutionOpeningProbability_bounds (positive n) (silentBound n)
      (nonnegative n)).2) relative
  simpa only [sub_zero] using tendsto_const_nhds.sub vanishes

/-- If source false trembles vanish faster than deferral, both vanish, and
deferral is positive, the same two-turn action payoff regret tends to zero.
The rate correction leaves the initial deferral probability tending to zero. -/
theorem twoSlotResolutionOpeningProbability_slow_regret
    (silent weight : ℕ → ℝ) (positiveWeight : ∀ n, 0 < weight n)
    (silentVanishes : Tendsto silent atTop (nhds 0))
    (weightVanishes : Tendsto weight atTop (nhds 0))
    (relative : Tendsto (fun n => silent n / weight n) atTop (nhds 0)) :
    Tendsto (fun n => 1 - twoSlotResolutionOpeningProbability (silent n) (weight n))
      atTop (nhds 0) := by
  have expression (n : ℕ) : twoSlotResolutionOpeningProbability (silent n) (weight n) =
      (1 - silent n) / (1 + (silent n / weight n) * (1 - weight n)) := by
    unfold twoSlotResolutionOpeningProbability
    have nonzero := (positiveWeight n).ne'
    have denominator : 1 + (silent n / weight n) * (1 - weight n) =
        (silent n * (1 - weight n) + weight n) / weight n := by
      field_simp [nonzero]
      ring
    rw [denominator, div_div_eq_mul_div]
  have constant : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have denominator : Tendsto (fun n => 1 + (silent n / weight n) * (1 - weight n))
      atTop (nhds 1) := by
    simpa only [sub_zero, zero_mul, add_zero] using constant.add
      (relative.mul (constant.sub weightVanishes))
  have opens : Tendsto (fun n => twoSlotResolutionOpeningProbability (silent n) (weight n))
      atTop (nhds 1) := by
    simp_rw [expression]
    convert (constant.sub silentVanishes).div denominator one_ne_zero using 1
    norm_num
  simpa only [sub_self] using constant.sub opens

end Vegas
