/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobDirtyPrefix
import Vegas.Examples.LateOpeningRuntimeBobRecallStability
import Vegas.Examples.LateOpeningRuntimeBobSubmissionService
import Interaction.ReactiveReceiptIdentity

/-! # Actual receiver binding service after arbitrary earlier actions

The actual native binding fiber has one earlier receiver action. Its envelope
has already received a permanent receipt, so silence causes protected service
to wait; new submissions are included under their actual next message ID.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingTransport

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeBobBindingService
  LateOpeningRuntimeBobRecallStability LateOpeningRuntimeBobDirtyPrefix
  LateOpeningRuntimeBobSubmissionService LateOpeningRuntimeBobResponseState

/-- The first native binding callback has exactly one earlier receiver action. -/
theorem binding_history_prior_action (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩)) :
    ∃ response : app.Action,
      (execution.recall bob).map ReactiveApplication.PlayerEntry.action = [response] := by
  classical
  let players := rawMenu.uniformResponses
  have uniform := rawMenu.roundSupported_uniform initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  obtain ⟨budget, count, before, command, length, beforeSupported, selected,
    actor, observed⟩ := uniform
  change execution.environmentRecall.length + 14 = 26 at budget
  have cursor : execution.environmentRecall.length = 12 := by omega
  change execution.environmentRecall.length = count + 1 at length
  have countEq : count = 11 := by omega
  subst count
  have beforeLength := app.roundsFrom_recall initial
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 11 before beforeSupported
  have commandEq : command = .activate bob := by
    change command ∈ (stageChoice weight nonnegative before.environmentRecall.length _).support
      at selected
    rw [beforeLength] at selected
    exact (PMF.mem_support_pure_iff _ _).mp selected
  subst command
  have currentRecall := congrFun (app.environmentStep_recall before execution
    (.activate bob) observed) bob
  unfold ReactiveApplication.roundsFrom at beforeSupported
  obtain ⟨state, stateSupported, beforeReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ beforeSupported)
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 5 6] at beforeReached
  obtain ⟨responded, five, six⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ beforeReached)
  rw [app.runRounds_add (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 4 1] at five
  obtain ⟨prior, four, fifth⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ five)
  have priorSupported : prior ∈ (app.roundsFrom initial
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 4).support :=
    by
      change prior ∈ (initial.bind fun state => app.runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) players 4
        (ReactiveApplication.Execution.initial app state)).support
      rw [PMF.support_bind]
      exact Set.mem_iUnion₂.mpr ⟨state, stateSupported, four⟩
  have priorLength := app.roundsFrom_recall initial
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 4 prior priorSupported
  have priorEmpty : prior.recall bob = [] := by
    have kept := before_first_callback_recall weight nonnegative players 4
      (ReactiveApplication.Execution.initial app state) prior (by change 4 ≤ 4; omega) four
    exact kept
  simp only [ReactiveApplication.runRounds, PMF.bind_pure] at fifth
  obtain ⟨earlyCommand, earlySelected, earlyDispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ fifth)
  have earlyCommandEq : earlyCommand = .activate bob := by
    change earlyCommand ∈ (stageChoice weight nonnegative prior.environmentRecall.length _).support
      at earlySelected
    rw [priorLength] at earlySelected
    exact (PMF.mem_support_pure_iff _ _).mp earlySelected
  subst earlyCommand
  obtain ⟨early, activated, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ earlyDispatched)
  have earlyEmpty : early.recall bob = [] := by
    rw [app.environmentStep_recall prior early (.activate bob) activated, priorEmpty]
  obtain ⟨response, _, respondedEq⟩ := PMF.support_map .. ▸ resumed
  subst responded
  have respondedLength := app.round_environmentRecall_length
    (LateOpeningRuntimeService.scheduler weight nonnegative) players prior
    (early.respond app bob response) fifth
  have earlyLength : (early.respond app bob response).environmentRecall.length = 5 := by omega
  have beforeRecall := before_binding_recall weight nonnegative players 6
    (early.respond app bob response) before (by omega) (by omega) six
  have responseActions : (execution.recall bob).map ReactiveApplication.PlayerEntry.action =
      [response] := by
    rw [currentRecall, beforeRecall, app.respond_actions, earlyEmpty]
    rfl
  exact ⟨response, responseActions⟩

/-- Actual protected binding service for arbitrary earlier receiver actions. -/
def servicedBinding (execution : app.Execution) (response : app.Action) : app.Execution :=
  match response.transmission with
  | some material => servicedSubmission execution material
  | none =>
      let submitted := execution.respond app bob response
      { submitted with environmentRecall := submitted.environmentRecall ++
        [⟨submitted.observeEnvironment app, ReactiveApplication.Command.wait⟩] }

theorem servicedBinding_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (response : app.Action) (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (execution.respond app bob response) = PMF.pure (servicedBinding execution response) := by
  cases response with
  | mk transmission =>
      cases transmission with
      | some material =>
          exact submission_round weight nonnegative 14 execution
            (rawMenu.toRawTrace _ _ _ trace) material players
      | none =>
          have chosen := protected_response_scheduler weight nonnegative
            ⟨14, some bob, execution⟩ (rawMenu.toRawTrace _ _ _ trace) bob rfl ⟨none⟩ (Or.inl rfl)
          have selected : latestAuthor bob
              ((execution.respond app bob ⟨none⟩).observeEnvironment app) = .wait :=
            latestAuthor_bob_wait_of_active weight nonnegative ⟨14, some bob, execution⟩
              (rawMenu.toRawTrace _ _ _ trace) (by simp)
          rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind,
            ReactiveApplication.dispatch]
          simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
            PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
          rfl

theorem servicedBinding_physical (weight : ℝ) (nonnegative : 0 ≤ weight)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (response : app.Action) :
    (servicedBinding execution response).application =
      LateOpeningRuntimeBobResponseState.responseState execution response := by
  cases response with
  | mk transmission =>
      cases transmission with
      | none => rfl
      | some material =>
          exact submission_physical weight nonnegative 14 execution
            (rawMenu.toRawTrace _ _ _ trace) material
theorem serviced_binding_same_information (weight : ℝ) (nonnegative : 0 ≤ weight)
    (first second : app.Execution)
    (firstTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, first⟩))
    (secondTrace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, second⟩))
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob) (response : app.Action) :
    (servicedBinding first response).application.config.store (.inr bobBindEvent) =
      (servicedBinding second response).application.config.store (.inr bobBindEvent) := by
  rw [servicedBinding_physical weight nonnegative first firstTrace,
    servicedBinding_physical weight nonnegative second secondTrace]
  have same := responseState_same_view first second
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
        (rawMenu.toRawTrace _ _ _ firstTrace))
    (app.history_inputRecall initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)
        (rawMenu.toRawTrace _ _ _ secondTrace)) sameRecall sameView response
  have stores := congrArg (fun view : PlayerView nativeGraph => view.observation.store) same
  have visible : nativeGraph.fieldVisibleTo bob (.inr bobBindEvent) := by decide
  have stored := congrFun stores (.inr bobBindEvent)
  change nativeGraph.playerStore bob (responseState first response).config.store
      (.inr bobBindEvent) =
    nativeGraph.playerStore bob (responseState second response).config.store
      (.inr bobBindEvent) at stored
  simpa only [nativeGraph.playerStore_of_visible bob _ _ visible] using stored

end Vegas.Examples.LateOpeningRuntimeBobBindingTransport
