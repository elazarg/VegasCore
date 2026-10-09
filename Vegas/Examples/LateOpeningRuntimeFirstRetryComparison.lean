/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeRetryWitness
import Vegas.Examples.LateOpeningRuntimeBindingFactors

/-! # Retry errors in the original first-response mixture

The comparison retains every original first response, every early receiver
response and their exact probabilities. Only the final sender response after
a genuine first opening and early receiver silence is replaced by silence.
This is a comparison of physical kernels, not a replacement information model.
Its total variation error is at most the uniform native retry bound times the
original genuine first-emission probability.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFirstRetryComparison

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLatePrefixKernel LateOpeningRuntimeLateResponseKernel
  LateOpeningRuntimeFirstObservation LateOpeningRuntimeBobBindingService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

abbrev Profile := ∀ who,
  (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who

def players (profile : Profile weight nonnegative) : Player → app.Policy :=
  rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile

def firstResponses (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) :
    PMF app.Action :=
  players weight nonnegative profile alice ((firstLateDecision bit label).recall alice)
    ((firstLateDecision bit label).observe app alice)

def earlyObserved (bit : Bool) (label : Fin 3) (submission : app.Submission) (seen : Bool) :
    app.Execution :=
  (firstSent bit label ⟨some submission⟩).sampledActivation app bob
    (if seen then {(alice, 0)} else ∅)

def quietRetry (bit : Bool) (label : Fin 3) (submission : app.Submission) (seen : Bool) :
    PMF app.Execution :=
  settlementKernel weight nonnegative
    ((finalDecision bit label ⟨some submission⟩
      (if seen then {(alice, 0)} else ∅)).respond app alice ⟨none⟩)

open Classical in
def earlyComparison (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3)
    (submission : app.Submission) (seen : Bool) : PMF app.Execution :=
  let observed := earlyObserved bit label submission seen
  (players weight nonnegative profile bob (observed.recall bob)
    (observed.observe app bob)).bind fun response =>
      if response = ⟨none⟩ then quietRetry weight nonnegative bit label submission seen
      else afterEarly weight nonnegative (players weight nonnegative profile)
        (observed.respond app bob response)

open Classical in
def firstComparison (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3)
    (response : app.Action) : PMF app.Execution :=
  match response.transmission with
  | none => firstBindingLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response (players weight nonnegative profile)
  | some submission =>
      if LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          submission then
        mix (1 / 2) (by norm_num) (by norm_num)
          (earlyComparison weight nonnegative profile bit label submission true)
          (earlyComparison weight nonnegative profile bit label submission false)
      else firstBindingLaw weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response (players weight nonnegative profile)

def originalLaw (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) :
    PMF app.Execution :=
  (firstResponses weight nonnegative profile bit label).bind fun response =>
    firstBindingLaw weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response (players weight nonnegative profile)

def comparisonLaw (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) :
    PMF app.Execution :=
  (firstResponses weight nonnegative profile bit label).bind
    (firstComparison weight nonnegative profile bit label)

def genuineProbability (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3) :
    ℝ :=
  ((firstResponses weight nonnegative profile bit label).toOuterMeasure
    {response | GenuineResponse weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        response}).toReal

/-- The original early receiver response remains an exact multiplier for
every event whose complete receiver record contains only silent responses. -/
theorem early_comparison_event_probability (profile : Profile weight nonnegative)
    (bit : Bool) (label : Fin 3) (submission : app.Submission) (seen : Bool)
    (event : Set app.Execution) (quiet : ∀ final ∈ event, SilentRecall final) :
    ((earlyComparison weight nonnegative profile bit label submission seen).toOuterMeasure
      event).toReal =
        (players weight nonnegative profile bob
          ((earlyObserved bit label submission seen).recall bob)
          ((earlyObserved bit label submission seen).observe app bob) ⟨none⟩).toReal *
          ((quietRetry weight nonnegative bit label submission seen).toOuterMeasure event).toReal :=
    by
  classical
  unfold earlyComparison
  rw [toReal_toOuterMeasure_bind]
  calc
    _ = expect (players weight nonnegative profile bob
        ((earlyObserved bit label submission seen).recall bob)
        ((earlyObserved bit label submission seen).observe app bob))
        (fun response => if (⟨none⟩ : app.Action) = response then
          ((quietRetry weight nonnegative bit label submission seen).toOuterMeasure event).toReal
            else 0) := by
      apply expect_congr_on_support
      intro response _
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => simp only [↓reduceIte]
      | some raw =>
          rw [ite_eq_right (by intro same; cases same)]
          rw [transmitted_early_silent_event_zero weight nonnegative
            (players weight nonnegative profile) (earlyObserved bit label submission seen)
              raw event quiet]
          simp
    _ = _ := expect_ite_eq _ _ _

variable (profile : Profile weight nonnegative) (bit : Bool) (label : Fin 3)
  (error : ℝ) (errorNonnegative : 0 ≤ error)
  (bound : ∀ actual : LateOpeningRuntimeAliceTremble.PendingOpeningSite weight nonnegative,
    LateOpeningRuntimeAliceTremble.emissionProbability
      weight nonnegative profile actual.1 ≤ error)

include errorNonnegative bound in
theorem early_comparison_close (submission : app.Submission)
    (available : (⟨some submission⟩ : app.Action) ∈ rawMenu.actions alice
      ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice))
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) :
    PMF.WithinTV error
      ((app.invoke (players weight nonnegative profile) bob
        (earlyObserved bit label submission seen)).bind
          (afterEarly weight nonnegative (players weight nonnegative profile)))
      (earlyComparison weight nonnegative profile bit label submission seen) := by
  unfold ReactiveApplication.invoke earlyComparison
  rw [PMF.bind_map]
  apply PMF.WithinTV.bind_right
  intro response _
  simp only [Function.comp_apply]
  by_cases quiet : response = ⟨none⟩
  · subst response
    rw [ite_eq_left rfl]
    change PMF.WithinTV error
      (afterEarly weight nonnegative (players weight nonnegative profile)
        (earlyQuiet bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅))) _
    rw [after_early_quiet_law]
    exact LateOpeningRuntimeRetryWitness.genuine_alias_response_close_quiet weight
      nonnegative bit label submission available seen genuine profile error bound
  · rw [ite_eq_right quiet]
    exact (PMF.WithinTV.refl _).mono errorNonnegative

include errorNonnegative bound in
theorem genuine_first_comparison_close (submission : app.Submission)
    (available : (⟨some submission⟩ : app.Action) ∈ rawMenu.actions alice
      ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice))
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) :
    PMF.WithinTV error
      (firstBindingLaw weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          ⟨some submission⟩ (players weight nonnegative profile))
      (firstComparison weight nonnegative profile bit label ⟨some submission⟩) := by
  rw [transmitted_binding_law]
  have physical : sent weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        ⟨some submission⟩ = firstSent bit label ⟨some submission⟩ := rfl
  rw [physical]
  simp only [firstComparison, ite_eq_left genuine]
  let fair : PMF Bool := mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure true) (PMF.pure false)
  have close : PMF.WithinTV error
      (fair.bind fun seen => (app.invoke (players weight nonnegative profile) bob
        (earlyObserved bit label submission seen)).bind
          (afterEarly weight nonnegative (players weight nonnegative profile)))
      (fair.bind (earlyComparison weight nonnegative profile bit label submission)) := by
    apply PMF.WithinTV.bind_right
    intro seen _
    exact early_comparison_close weight nonnegative profile bit label error errorNonnegative
      bound submission available genuine seen
  simpa only [fair, mix_bind, PMF.pure_bind, earlyObserved, Bool.false_eq_true,
    ↓reduceIte] using close

include errorNonnegative bound in
open Classical in
theorem response_comparison_close (response : app.Action)
    (available : response ∈ rawMenu.actions alice ((firstLateDecision bit label).recall alice)
      ((firstLateDecision bit label).observe app alice)) :
    PMF.WithinTV
      (if GenuineResponse weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response then error else 0)
      (firstBindingLaw weight nonnegative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          response (players weight nonnegative profile))
      (firstComparison weight nonnegative profile bit label response) := by
  classical
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have empty : ¬ GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            (⟨none⟩ : app.Action) := by
        rintro ⟨_, same, _⟩
        cases same
      rw [ite_eq_right empty]
      exact PMF.WithinTV.refl _
  | some submission =>
      have emitted : GenuineResponse weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            (⟨some submission⟩ : app.Action) ↔
          LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
            (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
              submission := by
        constructor
        · rintro ⟨other, same, genuine⟩
          cases Option.some.inj same
          exact genuine
        · exact fun genuine => ⟨submission, rfl, genuine⟩
      by_cases genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
          (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
            submission
      · rw [ite_eq_left (emitted.mpr genuine)]
        exact genuine_first_comparison_close weight nonnegative profile bit label error
          errorNonnegative bound submission available genuine
      · rw [ite_eq_right (fun present => genuine (emitted.mp present))]
        have unchanged : firstComparison weight nonnegative profile bit label ⟨some submission⟩ =
            firstBindingLaw weight nonnegative
              (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
                ⟨some submission⟩ (players weight nonnegative profile) := by
          simp only [firstComparison, ite_eq_right genuine]
        rw [unchanged]
        exact PMF.WithinTV.refl _

include errorNonnegative bound in
theorem original_close_comparison :
    PMF.WithinTV (error * genuineProbability weight nonnegative profile bit label)
      (originalLaw weight nonnegative profile bit label)
      (comparisonLaw weight nonnegative profile bit label) := by
  classical
  let decision := LateOpeningRuntimeAliceFirstWitness.decisionHistory
    weight nonnegative bit label
  let cost : app.Action → ℝ := fun response =>
    if GenuineResponse weight nonnegative decision response then error else 0
  have integrable : PayoffIntegrable (firstResponses weight nonnegative profile bit label)
      cost := payoffIntegrable_of_bounded _ _ (C := |error|) fun response => by
    simp only [cost]
    split_ifs <;> simp
  have close := PMF.WithinTV.bind_right_expect
    (firstResponses weight nonnegative profile bit label) cost integrable
      (first := fun response => firstBindingLaw weight nonnegative decision response
        (players weight nonnegative profile))
      (second := firstComparison weight nonnegative profile bit label) (fun response supported => by
        have available := rawMenu.decode_embedPolicy_covered initial
          LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
          alice (profile alice) ((firstLateDecision bit label).recall alice)
            ((firstLateDecision bit label).observe app alice) response supported
        exact response_comparison_close weight nonnegative profile bit label error
          errorNonnegative bound response available)
  have value : expect (firstResponses weight nonnegative profile bit label) cost =
      error * genuineProbability weight nonnegative profile bit label := by
    have point : cost = fun response => error *
        if GenuineResponse weight nonnegative decision response then 1 else 0 := by
      funext response
      simp only [cost]
      split_ifs <;> simp
    rw [point, expect_const_mul]
    change error * expect (firstResponses weight nonnegative profile bit label)
      (fun response => if response ∈ {response | GenuineResponse weight nonnegative
        decision response} then 1 else 0) = _
    rw [expect_indicator]
    rfl
  rw [value] at close
  exact close

end Vegas.Examples.LateOpeningRuntimeFirstRetryComparison
