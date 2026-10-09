/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLateAcceptance

/-! # Legal raw histories at the accepted late-opening answer decision

The concrete sample and inclusion branches are reached in the full bounded
raw protocol. No restricted choice set or hypothetical information state is
used to obtain the answer records.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeLateHistories

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix LateOpeningRuntimeLateAcceptance

private theorem observed_trace (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨21, none, bobObserved bit label slot seen⟩)) := by
  fin_cases slot
  · exact bobObserved_first_trace weight nonnegative bit label seen
  · have unseen : seen = false := samplePossible.resolve_left (by decide)
    subst seen
    exact bobObserved_second_trace weight nonnegative bit label

theorem beforeLottery_trace (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨18, none, beforeLottery bit label slot seen⟩)) := by
  obtain ⟨prior⟩ := observed_trace weight nonnegative bit label slot seen samplePossible
  apply rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      (latePlayers_covered bit slot) 18 3 (bobObserved bit label slot seen) _ prior
  rw [beforeLottery_run]
  simp

/-- Every possible sample branch and every positive finite lottery weight
give a genuine accepted-opening raw history. -/
theorem acceptedLottery_trace (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨17, none, acceptedLottery bit label slot seen⟩)) := by
  obtain ⟨prior⟩ := beforeLottery_trace weight nonnegative bit label slot seen samplePossible
  apply rawMenu.trace_round initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      (latePlayers_covered bit slot) 17 (beforeLottery bit label slot seen) _ prior
  rw [lottery_round]
  exact mem_support_mix_left (inclusionProbability weight)
    (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
    (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
    (by unfold inclusionProbability MessageNetwork.inclusionMass; positivity)
    (by simp)

theorem beforeAnswer_trace (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨15, none, beforeAnswer bit label slot seen⟩)) := by
  obtain ⟨prior⟩ := acceptedLottery_trace weight nonnegative positive bit label slot seen
    samplePossible
  apply rawMenu.trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      (latePlayers_covered bit slot) 15 2 (acceptedLottery bit label slot seen) _ prior
  rw [beforeAnswer_run]
  simp

/-- Bob's accepted-success answer record is an actual active decision history
of the full raw game, for either late sending time and every possible sample. -/
theorem answerDecision_trace (weight : ℝ) (nonnegative : 0 ≤ weight) (positive : 0 < weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool)
    (samplePossible : slot = 0 ∨ seen = false) :
    Nonempty ((rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, answerDecision bit label slot seen⟩)) := by
  obtain ⟨prior⟩ := beforeAnswer_trace weight nonnegative positive bit label slot seen
    samplePossible
  apply rawMenu.trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 (beforeAnswer bit label slot seen)
      (answerDecision bit label slot seen) (.activate bob) prior
  · change (.activate bob : app.Command) ∈
      (stageChoice weight nonnegative (beforeAnswer bit label slot seen).environmentRecall.length
        ((beforeAnswer bit label slot seen).observeEnvironment app)).support
    have cursor : (beforeAnswer bit label slot seen).environmentRecall.length = 11 := rfl
    rw [cursor]
    simp [stageChoice]
  · rw [answerDecision_activation]
    simp

end Vegas.Examples.LateOpeningRuntimeLateHistories
