/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBindingObservation
import Vegas.Examples.LateOpeningRuntimeLateHistories

/-! # Actual receiver information after an omitted late opening -/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBindingObservationWitness

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeLateHistories
  LateOpeningRuntimeLatePrefixKernel LateOpeningRuntimeBindingObservation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

theorem beforeFailedAnswer_trace (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨15, none, beforeFailedAnswer bit label slot seen⟩)) := by
  obtain ⟨before⟩ := beforeLottery_trace weight nonnegative bit label slot seen samplePossible
  apply rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      (latePlayers_covered bit slot) 15 3 (beforeLottery bit label slot seen) _ before
  rw [settlement_rounds weight nonnegative (latePlayers bit slot) _ rfl, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨none, ?_, ?_⟩
  · rw [MessageNetwork.chooseWithOutside]
    apply mem_support_mix_right _ _ _
      (MessageNetwork.inclusionMass_below_one weight nonnegative _)
    simp
  · rw [omitted_settlement]
    simp

theorem failedAnswerDecision_trace (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) (samplePossible : slot = 0 ∨ earlySeen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, failedAnswerDecision bit label slot earlySeen finalSeen⟩)) := by
  obtain ⟨before⟩ := beforeFailedAnswer_trace weight nonnegative bit label slot earlySeen
    samplePossible
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14
      (beforeFailedAnswer bit label slot earlySeen)
      (failedAnswerDecision bit label slot earlySeen finalSeen) (.activate bob) before
  · change (.activate bob : app.Command) ∈ (stageChoice weight nonnegative
      (beforeFailedAnswer bit label slot earlySeen).environmentRecall.length _).support
    have cursor : (beforeFailedAnswer bit label slot earlySeen).environmentRecall.length = 11 := rfl
    rw [cursor]
    simp [stageChoice]
  · have activation : (beforeFailedAnswer bit label slot earlySeen).environmentStep app
        (.activate bob) =
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (failedAnswerDecision bit label slot earlySeen true))
        (PMF.pure (failedAnswerDecision bit label slot earlySeen false)) := by
      simpa only [branchLaw, omitted_settlement, PMF.pure_bind] using
        omitted_branch_law bit label slot earlySeen
    rw [activation]
    cases finalSeen
    · exact mem_support_mix_right _ _ _ (by norm_num) (by simp)
    · exact mem_support_mix_left _ _ _ (by norm_num) (by simp)

/-- These exact remembered records and current views are native information
sites in the complete bounded raw game, for every finite lottery weight. -/
theorem failed_information_representative (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) (samplePossible : slot = 0 ∨ earlySeen = false) :
    ∃ (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
      (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
        bob site.1),
      representative.1.state =
          some ⟨14, some bob, failedAnswerDecision bit label slot earlySeen finalSeen⟩ ∧
        site.1 = some (bobInformation
          (failedAnswerDecision bit label slot earlySeen finalSeen)) := by
  obtain ⟨trace⟩ := failedAnswerDecision_trace weight nonnegative bit label slot earlySeen finalSeen
    samplePossible
  let history : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).History :=
    ⟨some ⟨14, some bob, failedAnswerDecision bit label slot earlySeen finalSeen⟩, trace⟩
  have running : ¬ (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).terminal history.state := by
    change ¬ (14 = 0 ∧ some bob = none)
    simp
  obtain ⟨site, same⟩ :=
    (LateOpeningRuntimeNash.model weight nonnegative).exists_informationSite_of_active
      bob history running rfl
  refine ⟨site, ⟨history, same.symm⟩, rfl, ?_⟩
  change site.1 = (rawMenu.signals _ _ _).infoOf bob history.trace at same
  rw [rawMenu.info] at same
  exact same

end Vegas.Examples.LateOpeningRuntimeBindingObservationWitness
