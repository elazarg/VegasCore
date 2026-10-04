/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SequentialValidation.History

/-! # A legal unusable owner response in the one-pass disclosure calendar

Alice may omit all three early submissions. The calendar still activates Bob
at position six, before any timeout. His dependent guess is then not ready.
This is a legal history of the actual bounded native arena, rather than an
alternative schedule or an application state assumed to be reachable.
-/

noncomputable section

namespace Vegas.Examples.CommunicationServiceOmission

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open SequentialValidation

def silentWindow (execution : nativeApp.Execution) (who : Bool) : nativeApp.Execution :=
  let responded := (nativeActivate execution who).respond nativeApp who ⟨none⟩
  nativeRecord responded responded .wait

theorem silentWindow_length (execution : nativeApp.Execution) (who : Bool) :
    (silentWindow execution who).environmentRecall.length =
      execution.environmentRecall.length + 2 := by
  simp only [silentWindow, nativeRecord, List.length_append, List.length_singleton]
  rw [nativeApp.respond_environmentRecall]
  simp [nativeActivate, nativeRecord]

theorem silentWindow_pending (execution : nativeApp.Execution) (who : Bool) :
    (silentWindow execution who).network.pending = execution.network.pending := rfl

theorem silentWindow_config (execution : nativeApp.Execution) (who : Bool) :
    (silentWindow execution who).application.config = execution.application.config := rfl

theorem select_empty (execution : nativeApp.Execution)
    (eligible : Message Bool (WitnessedPacket nativeGraph) → Bool)
    (empty : execution.network.pending = []) :
    nativeApp.uniformInstruction dependencyCondition execution.environmentRecall
      (execution.observeEnvironment nativeApp) (.select eligible) = PMF.pure .wait := by
  change (MessageNetwork.uniformPending _ execution.network.pending).map _ = _
  rw [empty, MessageNetwork.uniformPending_empty, PMF.pure_map]
  rfl

def silentWindowTrace (remaining : Nat) (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool)
    (trace : nativeArena.Trace (some ⟨remaining + 2, none, execution⟩))
    (activate : nativeCalendar execution.environmentRecall.length = .activate who)
    (select : nativeCalendar (execution.environmentRecall.length + 1) =
      .select (eventProposal event who))
    (empty : execution.network.pending = []) :
    nativeArena.Trace (some ⟨remaining, none, silentWindow execution who⟩) := by
  let activated := nativeActivate execution who
  let responded := activated.respond nativeApp who ⟨none⟩
  have second : nativeArena.Trace (some ⟨remaining + 1, some who, activated⟩) :=
    nativeEnvironmentTrace (remaining + 1) execution activated trace (.activate who)
      (native_schedule execution _ activate) (native_activate_law execution who)
  have third : nativeArena.Trace (some ⟨remaining + 1, none, responded⟩) :=
    nativeResponseTrace (remaining + 1) activated who second ⟨none⟩ (by
      rw [MessageBounds.menu_mem]
      exact ⟨trivial, rfl⟩)
  have selectPosition : nativeCalendar responded.environmentRecall.length =
      .select (eventProposal event who) := by
    dsimp only [responded]
    rw [nativeApp.respond_environmentRecall]
    simpa only [activated, nativeActivate, nativeRecord, List.length_append,
      List.length_singleton] using select
  apply nativeEnvironmentTrace remaining responded (silentWindow execution who) third .wait
  · rw [native_schedule responded _ selectPosition]
    exact select_empty responded _ empty
  · rw [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl

def silentFirst (bit : Bool) : nativeApp.Execution :=
  silentWindow (nativeInitialExecution bit) false

def silentSecond (bit : Bool) : nativeApp.Execution :=
  silentWindow (silentFirst bit) false

def silentThird (bit : Bool) : nativeApp.Execution :=
  silentWindow (silentSecond bit) false

def silentBob (bit : Bool) : nativeApp.Execution :=
  nativeActivate (silentThird bit) true

def silentBobTrace (bit : Bool) :
    nativeArena.Trace (some ⟨45, some true, silentBob bit⟩) := by
  have first : nativeArena.Trace (some ⟨50, none, silentFirst bit⟩) :=
    silentWindowTrace 50 (nativeInitialExecution bit) bindingEvent false
      (nativeSetupTrace bit) rfl rfl rfl
  have firstLength : (silentFirst bit).environmentRecall.length = 2 :=
    silentWindow_length _ _
  have second : nativeArena.Trace (some ⟨48, none, silentSecond bit⟩) :=
    silentWindowTrace 48 (silentFirst bit) dummyEvent false first
      (by rw [firstLength]; rfl) (by rw [firstLength]; rfl) rfl
  have secondLength : (silentSecond bit).environmentRecall.length = 4 := by
    rw [silentSecond, silentWindow_length, firstLength]
  have third : nativeArena.Trace (some ⟨46, none, silentThird bit⟩) :=
    silentWindowTrace 46 (silentSecond bit) secretEvent false second
      (by rw [secondLength]; rfl) (by rw [secondLength]; rfl) rfl
  have thirdLength : (silentThird bit).environmentRecall.length = 6 := by
    rw [silentThird, silentWindow_length, secondLength]
  exact nativeEnvironmentTrace 45 _ (silentBob bit) third (.activate true)
    (native_schedule (silentThird bit) (.activate true) (by rw [thirdLength]; rfl))
    (native_activate_law _ _)

/-- A genuine Bob information history has no enabled source guess: the first
binding is still unfinished, and the calendar offers Bob no later response. -/
theorem silent_bob_not_ready (bit : Bool) :
    ¬(silentBob bit).application.config.cut.Ready guessEvent := by
  change ¬(nativeStart bit).config.cut.Ready guessEvent
  cases bit <;> decide

theorem legal_unusable_bob_response (bit : Bool) :
    ∃ control : nativeApp.Control,
      Nonempty (nativeArena.Trace (some control)) ∧ control.actor = some true ∧
      ¬control.execution.application.config.cut.Ready guessEvent :=
  ⟨⟨45, some true, silentBob bit⟩, ⟨silentBobTrace bit⟩, rfl, silent_bob_not_ready bit⟩

end Vegas.Examples.CommunicationServiceOmission
