/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingTimingPosterior
import Interaction.ScheduledChoicePosterior

/-! # The timing posterior when the source decision can itself be silent

An actual first-turn silence downweights timing index zero by the canonical
decision's silent-response probability. It does not remove that index when
the source can choose silence. The posterior comes from actual own recall,
with its initial law derived from the absence of earlier turns at this event.
This is a local timing calculation, not source-belief transport or an
equilibrium embedding.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A first-turn silence retains the selected timing index in proportion to
the actual source decision's silent likelihood. No earlier posterior formula
is assumed. This also covers silence caused by a closed opportunity gate. -/
theorem sourceServiceTurnFamily_first_silence_posterior
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (timing : PMF (Fin (turns + 1)))
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks who event (middle.recall who)
      (middle.observe (application setup leaks) who) = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal)
    (slot : Fin (turns + 1)) :
    let app := application setup leaks
    let silent := ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      (middle.recall who) (middle.observe app who)) ⟨none⟩).toReal
    (((app.policyMixture timing (sourceServiceTurnFamily setup leaks bound profile who event
      turns)).posterior ((middle.respond app who ⟨none⟩).recall who)) slot).toReal =
        (timing slot).toReal * (if slot.val < 1 then silent else 1) /
          (1 - (1 - silent) * (timing 0).toReal) := by
  classical
  dsimp only
  let app := application setup leaks
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let entry : app.PlayerEntry := ⟨middle.observe app who, ⟨none⟩, none⟩
  let deciding := sourceServiceCanonicalOpportunity setup leaks bound profile who event
    (middle.recall who) entry.beforeView
  let silent := (deciding ⟨none⟩).toReal
  let probability := 1 - silent
  have bounded : silent ≤ 1 := pmf_toReal_apply_le_one deciding ⟨none⟩
  have nonnegative : 0 ≤ probability := sub_nonneg.mpr bounded
  have small : probability < 1 := by dsimp only [probability]; linarith
  have previous := sourceServiceTurnFamily_first_posterior (bound := bound) (profile := profile)
    timing _ _ first
  change (app.policyMixture timing family).posterior (middle.recall who) = timing at previous
  have old (selected : Fin (turns + 1)) :
      (((app.policyMixture timing family).posterior (middle.recall who)) selected).toReal =
        (timing selected).toReal * (if selected.val < (0 : Fin (turns + 1)).val then
          1 - probability else 1) / PMF.deferredSurvival probability timing 0 := by
    rw [previous]
    simp only [Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, mul_one,
      PMF.deferredSurvival, PMF.timingPrefix_zero, mul_zero, sub_zero, div_one]
  have likelihood (selected : Fin (turns + 1)) :
      ((family selected (middle.recall who) entry.beforeView) entry.action).toReal =
        (if selected = 0 then 1 - probability else 1) *
          (((PMF.pure ⟨none⟩) : PMF app.Action) entry.action).toReal := by
    by_cases selectedNow : selected = 0
    · subst selected
      rw [show family 0 (middle.recall who) entry.beforeView = deciding from
        app.turnScheduledPolicy_selected _ _ _ _ _ _ first]
      simp only [entry, probability, silent, ↓reduceIte, PMF.pure_apply,
        ENNReal.toReal_one, mul_one, sub_sub_cancel]
    · have different : sourceServiceTurn setup leaks who event (middle.recall who)
          entry.beforeView ≠ some selected.val := by
        rw [first]
        intro same
        exact selectedNow (Fin.ext (Option.some.inj same).symm)
      rw [show family selected (middle.recall who) entry.beforeView =
        app.silentPolicy (middle.recall who) entry.beforeView from
          app.turnScheduledPolicy_unselected _ _ _ _ _ _ (fun _ same => by
            cases Option.some.inj same
            exact different)]
      simp only [entry, selectedNow, ↓reduceIte, ReactiveApplication.silentPolicy,
        PMF.pure_apply, ENNReal.toReal_one, mul_one]
  have update := app.scheduledChoice_posterior_step timing family probability nonnegative small
    (middle.recall who) entry 0 (PMF.pure ⟨none⟩) (by simp [entry]) likelihood old slot
  have denominator : PMF.deferredSurvival probability timing 1 =
      1 - probability * (timing 0).toReal := by
    change PMF.deferredSurvival probability timing ((0 : Fin (turns + 1)).val + 1) = _
    rw [PMF.deferredSurvival_succ, PMF.deferredSurvival]
    simp only [Fin.val_zero, PMF.timingPrefix_zero, mul_zero, sub_zero]
  have recallEq : (middle.respond app who ⟨none⟩).recall who = middle.recall who ++ [entry] := by
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
    rfl
  rw [recallEq]
  simpa only [Fin.val_zero, Nat.zero_add, denominator, probability, sub_sub_cancel] using update

/-- The actual response law differs from waiting by at most the posterior
mass of the current timing index, uniformly in the source profile. -/
theorem sourceServiceTurnFamily_waiting_response_error
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (timing : PMF (Fin (turns + 1))) (current : Fin (turns + 1))
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (atIndex : sourceServiceTurn setup leaks who event past view = some current.val)
    (response : (application setup leaks).Action) :
    let app := application setup leaks
    let family := sourceServiceTurnFamily setup leaks bound profile who event turns
    |(((app.policyMixture timing family).policy past view) response).toReal -
      ((app.silentPolicy past view) response).toReal| ≤
      (((app.policyMixture timing family).posterior past) current).toReal := by
  dsimp only
  let app := application setup leaks
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let post := (app.policyMixture timing family).posterior past
  let hazard := (post current).toReal
  let deciding := sourceServiceCanonicalOpportunity setup leaks bound profile who event past view
  let waiting := app.silentPolicy past view
  have nonnegative : 0 ≤ hazard := ENNReal.toReal_nonneg
  have decidNonnegative : 0 ≤ (deciding response).toReal := ENNReal.toReal_nonneg
  have waitNonnegative : 0 ≤ (waiting response).toReal := ENNReal.toReal_nonneg
  have decidBound := pmf_toReal_apply_le_one deciding response
  have waitBound := pmf_toReal_apply_le_one waiting response
  rw [sourceServiceTurnFamily_response_probability timing current past view atIndex response]
  change |hazard * (deciding response).toReal + (1 - hazard) * (waiting response).toReal -
    (waiting response).toReal| ≤ hazard
  calc
    _ = hazard * |(deciding response).toReal - (waiting response).toReal| := by
      rw [show hazard * (deciding response).toReal + (1 - hazard) *
        (waiting response).toReal - (waiting response).toReal =
          hazard * ((deciding response).toReal - (waiting response).toReal) by ring,
        abs_mul, abs_of_nonneg nonnegative]
    _ ≤ hazard * 1 := by
      apply mul_le_mul_of_nonneg_left _ nonnegative
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = _ := mul_one _

/-- With positive selected silence probability, one earlier silent response
makes the next geometric response close to silence by `weight / silent`.
The next view is explicit: its occurrence and protection are not inferred. -/
theorem sourceServiceTurnPolicy_first_silence_geometric_error
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks who event (middle.recall who)
      (middle.observe (application setup leaks) who) = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal)
    (owned : (graph setup).actor? event = some who)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1) (more : 0 < turns)
    (view : (application setup leaks).PlayerView)
    (next : sourceServiceTurn setup leaks who event
      ((middle.respond (application setup leaks) who ⟨none⟩).recall who) view = some 1)
    (response : (application setup leaks).Action) :
    let app := application setup leaks
    let past := (middle.respond app who ⟨none⟩).recall who
    |((sourceServiceTurnPolicy setup leaks bound turns
      (geometricTiming setup turns weight nonnegative bounded) profile who past view)
        response).toReal - ((PMF.pure ⟨none⟩) response).toReal| ≤
      weight / ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
        (middle.recall who) (middle.observe app who)) ⟨none⟩).toReal := by
  dsimp only
  let app := application setup leaks
  let past := (middle.respond app who ⟨none⟩).recall who
  let timing := geometricTurnLaw weight nonnegative bounded turns
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let current : Fin (turns + 1) := ⟨1, by omega⟩
  let silent := ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
    (middle.recall who) (middle.observe app who)) ⟨none⟩).toReal
  have silentBound : silent ≤ 1 := pmf_toReal_apply_le_one _ _
  have zeroMass : (timing 0).toReal = 1 - weight := by
    rw [geometricTurnLaw_apply_toReal]
    simp only [Fin.val_zero, more, ↓reduceIte, pow_zero, mul_one]
  have massBound : (timing current).toReal ≤ weight := by
    rw [geometricTurnLaw_apply_toReal]
    simp only [current]
    by_cases early : 1 < turns
    · rw [ite_eq_left early, pow_one]
      nlinarith
    · have finalIndex : turns = 1 := by omega
      rw [ite_eq_right early, finalIndex, pow_one]
  have lower : silent ≤ 1 - (1 - silent) * (timing 0).toReal := by
    rw [zeroMass]
    nlinarith [mul_nonneg (sub_nonneg.mpr silentBound) nonnegative]
  have denominator : 0 < 1 - (1 - silent) * (timing 0).toReal := lt_of_lt_of_le positive lower
  have hazardBound : (((app.policyMixture timing family).posterior past) current).toReal ≤
      weight / silent := by
    rw [sourceServiceTurnFamily_first_silence_posterior timing middle first positive current]
    simp only [current, lt_self_iff_false, ↓reduceIte, mul_one]
    exact (div_le_div_of_nonneg_right massBound denominator.le).trans
      (div_le_div_of_nonneg_left nonnegative positive lower)
  have serving : view.application.publicView.ownTurn? who = some event := by
    unfold sourceServiceTurn at next
    split at next
    · assumption
    · cases next
  rw [sourceServiceTurnPolicy_turn setup leaks bound turns _ profile who _ view event owned
    serving]
  exact (sourceServiceTurnFamily_waiting_response_error timing current past view next
    response).trans hazardBound

/-- When deferral vanishes relative to the selected silent likelihood, the
actual continuation after one earlier silence converges to staying silent.
This allows the source profile to vary along its own approximation sequence. -/
theorem sourceServiceTurnPolicy_first_silence_geometric_converges
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {who : Player} {event : (graph setup).EventId}
    (profiles : ℕ → BehavioralProfile setup.program)
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks who event (middle.recall who)
      (middle.observe (application setup leaks) who) = some 0)
    (positive : ∀ n, 0 < ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n)
      who event (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal)
    (owned : (graph setup).actor? event = some who)
    (weight : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (bounded : ∀ n, weight n ≤ 1)
    (more : 0 < turns) (view : (application setup leaks).PlayerView)
    (next : sourceServiceTurn setup leaks who event
      ((middle.respond (application setup leaks) who ⟨none⟩).recall who) view = some 1)
    (relative : Tendsto (fun n => weight n /
      ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n) who event
        (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal)
          atTop (nhds 0)) :
    let app := application setup leaks
    let past := (middle.respond app who ⟨none⟩).recall who
    PMFConvergesPointwise (fun n => sourceServiceTurnPolicy setup leaks bound turns
      (geometricTiming setup turns (weight n) (nonnegative n) (bounded n)) (profiles n) who
        past view) (PMF.pure ⟨none⟩) := by
  dsimp only
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro response
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun n => sourceServiceTurnPolicy_first_silence_geometric_error middle first (positive n)
      owned (weight n) (nonnegative n) (bounded n) more view next response) relative

/-- Positive actual silent likelihoods admit fully supported geometric timings
whose deferral vanishes fast enough for the after-silence continuation limit.
The source profile sequence may itself approach a deterministic choice. -/
theorem exists_first_silence_geometric_weights
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {who : Player} {event : (graph setup).EventId}
    (profiles : ℕ → BehavioralProfile setup.program)
    (middle : (application setup leaks).Execution)
    (first : sourceServiceTurn setup leaks who event (middle.recall who)
      (middle.observe (application setup leaks) who) = some 0)
    (positive : ∀ n, 0 < ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n)
      who event (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal)
    (owned : (graph setup).actor? event = some who) (more : 0 < turns)
    (view : (application setup leaks).PlayerView)
    (next : sourceServiceTurn setup leaks who event
      ((middle.respond (application setup leaks) who ⟨none⟩).recall who) view = some 1) :
    ∃ (weight : ℕ → ℝ) (positiveWeight : ∀ n, 0 < weight n)
      (below : ∀ n, weight n < 1), Tendsto weight atTop (nhds 0) ∧
        PMFConvergesPointwise (fun n => sourceServiceTurnPolicy setup leaks bound turns
          (geometricTiming setup turns (weight n) (positiveWeight n).le (below n).le)
            (profiles n) who ((middle.respond (application setup leaks) who ⟨none⟩).recall who)
              view) (PMF.pure ⟨none⟩) := by
  obtain ⟨weight, positiveWeight, below, vanishes, relative⟩ := exists_deferralWeights_faster
    (fun n => ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n) who event
      (middle.recall who) (middle.observe (application setup leaks) who)) ⟨none⟩).toReal) positive
  refine ⟨weight, positiveWeight, below, vanishes, ?_⟩
  exact sourceServiceTurnPolicy_first_silence_geometric_converges profiles middle first positive
    owned weight (fun n => (positiveWeight n).le) (fun n => (below n).le) more view next relative

end Vegas
