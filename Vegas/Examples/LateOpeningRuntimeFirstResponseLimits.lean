/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeFirstRetryComparison
import Vegas.Examples.LateOpeningRuntimeAliceFirstResponse

/-! # Limits of original first sender response laws

The actual initialized first-late callback is a legal bounded information
site. Its complete original raw response law converges along the given common
assessment sequence. In particular, genuine-emission and silence probabilities
retain their actual limiting values, without any positive reach assumption.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeFirstResponseLimits

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeFirstRetryComparison LateOpeningRuntimeFirstObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem firstResponses_converges
    (sequence : ℕ → Profile weight nonnegative) (target : Profile weight nonnegative)
    (converges : ∀ site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (bit : Bool) (label : Fin 3) :
    PMFConvergesPointwise (fun n => firstResponses weight nonnegative (sequence n) bit label)
      (firstResponses weight nonnegative target bit label) := by
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨22, some alice, firstLateDecision bit label⟩,
      (LateOpeningRuntimeAliceFirstWitness.firstLateDecision_trace
        weight nonnegative bit label).some⟩
  obtain ⟨site, information⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      alice history (by change ¬ (22 = 0 ∧ some alice = none); simp) rfl
  let representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1 := ⟨history, information.symm⟩
  have info := LateOpeningRuntimeAliceFirstResponse.site_information weight nonnegative site
    representative (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative
      bit label) rfl
  have decoded := (converges site).map (fun choice => choice.1.getD ⟨none⟩)
  rw [info] at decoded
  simpa only [firstResponses, players, ReactiveApplication.ResponseMenu.decodeProfile,
    ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
    ReactiveApplication.ResponseMenu.rawChoice, PMF.map_comp, Function.comp_def,
    LateOpeningRuntimeAliceFirstWitness.decisionHistory] using decoded

theorem genuineProbability_tendsto
    (sequence : ℕ → Profile weight nonnegative) (target : Profile weight nonnegative)
    (converges : ∀ site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (bit : Bool) (label : Fin 3) :
    Tendsto (fun n => genuineProbability weight nonnegative (sequence n) bit label) atTop
      (nhds (genuineProbability weight nonnegative target bit label)) := by
  classical
  let event : Set app.Action := {response | GenuineResponse weight nonnegative
    (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label) response}
  let indicator : app.Action → ℝ := fun response => if response ∈ event then 1 else 0
  have bound : ∀ response, |indicator response| ≤ 1 := by
    intro response
    dsimp only [indicator]
    split_ifs <;> norm_num
  have physical := firstResponses_converges weight nonnegative sequence target converges bit label
  have limit := physical.expect_of_bounded indicator bound
  simpa only [indicator, expect_indicator, genuineProbability, event] using limit

theorem silenceProbability_tendsto
    (sequence : ℕ → Profile weight nonnegative) (target : Profile weight nonnegative)
    (converges : ∀ site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice,
      PMFConvergesPointwise (fun n => sequence n alice site.1) (target alice site.1))
    (bit : Bool) (label : Fin 3) :
    Tendsto (fun n => (firstResponses weight nonnegative (sequence n) bit label ⟨none⟩).toReal)
      atTop (nhds ((firstResponses weight nonnegative target bit label ⟨none⟩).toReal)) :=
  (firstResponses_converges weight nonnegative sequence target converges bit label).toReal ⟨none⟩

end Vegas.Examples.LateOpeningRuntimeFirstResponseLimits
