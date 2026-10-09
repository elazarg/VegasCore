/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSeenLikelihood
import Vegas.Examples.LateOpeningRuntimeEarlyBobRationality

/-! # Original receiver silence at the actual early samples

Every canonical first-send or first-silence observation is a legal bounded
history. Its original receiver response law is silent under native sequential
rationality. The silence atoms in physical likelihoods therefore converge to
one along the same assessment sequence, including at unreached observations.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeObservation LateOpeningRuntimeFirstRetryComparison
  LateOpeningRuntimeEarlyBobInformation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def observed (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  (beforeBob bit label slot).sampledActivation app bob
    (if seen then {(alice, 0)} else ∅)

theorem observed_trace (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (possible : slot = 0 ∨ seen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, some bob, observed bit label slot seen⟩)) := by
  obtain ⟨firstTrace⟩ := LateOpeningRuntimeAliceFirstWitness.firstLateDecision_trace
    weight nonnegative bit label
  have available : (if slot.val = 0 then opening bit else ⟨none⟩) ∈
      rawMenu.actions alice ((firstLateDecision bit label).recall alice)
        ((firstLateDecision bit label).observe app alice) := by
    split_ifs
    · exact opening_in_raw_menu bit alice _ _
    · exact bounds.silent_available LateOpeningRuntimeService.runtime leaks alice _ _
  obtain ⟨sentTrace⟩ := rawMenu.trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 22 (firstLateDecision bit label)
      alice _ firstTrace available
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 21 (beforeBob bit label slot)
      (observed bit label slot seen) (.activate bob) sentTrace
  · change _ ∈ (PMF.pure _).support
    simp
  · rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
    refine ⟨if seen then {(alice, 0)} else ∅, ?_, rfl⟩
    apply (leaks_supported bob _ _).mpr
    rcases possible with rfl | rfl
    · cases seen
      · exact Finset.empty_subset _
      · rw [beforeBob_first_network]
        change ({(alice, 0)} : Finset (MessageId Player)) ⊆ {(alice, 0)}
        exact Finset.Subset.refl _
    · exact Finset.empty_subset _

def decision (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (possible : slot = 0 ∨ seen = false) : DecisionHistory weight nonnegative where
  execution := observed bit label slot seen
  trace := rawMenu.toRawTrace initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
      (observed_trace weight nonnegative bit label slot seen possible).some
  emptyRecall := rfl
  unresolved := by
    change aliceEvent ∉ ((firstLateDecision bit label).respond app alice
      (if slot.val = 0 then opening bit else ⟨none⟩)).application.config.cut.completed
    rw [(LateOpeningRuntimeService.runtime.reactive_respond_application leaks
      (firstLateDecision bit label) alice _).1]
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId)
    simp

theorem information_representative (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (possible : slot = 0 ∨ seen = false) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1),
      history.1.state = some ⟨21, some bob, observed bit label slot seen⟩ := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨21, some bob, observed bit label slot seen⟩,
      (observed_trace weight nonnegative bit label slot seen possible).some⟩
  obtain ⟨site, information⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      bob history (by change ¬ (21 = 0 ∧ some bob = none); simp) rfl
  exact ⟨site, ⟨history, information.symm⟩, rfl⟩

theorem sequentially_rational_response_law (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRational
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => LateOpeningRuntimeNash.payoff reward forfeit
        (fun actual => PMF.pure actual) deposit history.state who))
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (possible : slot = 0 ∨ seen = false) :
    players weight nonnegative assessment.strategy bob
      ((observed bit label slot seen).recall bob)
      ((observed bit label slot seen).observe app bob) = PMF.pure ⟨none⟩ := by
  obtain ⟨site, history, current⟩ := information_representative weight nonnegative bit label
    slot seen possible
  let actual := decision weight nonnegative bit label slot seen possible
  have silent := LateOpeningRuntimeEarlyBobRationality.sequentially_rational_early_response_law
    weight nonnegative site history actual current reward forfeit deposit forfeitNonnegative
      collateral assessment rational
  have info := LateOpeningRuntimeEarlyBobDecision.site_information
    weight nonnegative site history actual current
  unfold LateOpeningRuntimeEarlyBobDecision.responseLaw at silent
  rw [info] at silent
  simpa only [players, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def,
    actual, decision] using silent

end Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw
