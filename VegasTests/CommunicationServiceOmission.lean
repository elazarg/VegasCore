/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationHistory

/-! # A legal unusable owner response in the one-pass disclosure calendar

Alice may omit all three early submissions. The calendar still activates Bob
at position ten, before any timeout. His dependent guess is then not ready.
This is a legal history of the actual bounded native arena, rather than an
alternative schedule or an application state assumed to be reachable.
-/

noncomputable section

namespace VegasTests.CommunicationServiceOmission

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open SequentialValidation

def silentWindow (execution : nativeApp.Execution) (event : nativeGraph.EventId)
    (who : Bool) : nativeApp.Execution :=
  let responded := (nativeActivate (nativeGrant execution event) who).respond nativeApp who ⟨none⟩
  nativeRecord responded responded .wait

theorem silentWindow_length (execution : nativeApp.Execution) (event : nativeGraph.EventId)
    (who : Bool) :
    (silentWindow execution event who).environmentRecall.length =
      execution.environmentRecall.length + 3 := by
  simp only [silentWindow, nativeRecord, List.length_append, List.length_singleton]
  rw [nativeApp.respond_environmentRecall]
  simp [nativeActivate, nativeGrant, nativeRecord]

theorem silentWindow_pending (execution : nativeApp.Execution) (event : nativeGraph.EventId)
    (who : Bool) :
    (silentWindow execution event who).network.pending = execution.network.pending := rfl

theorem silentWindow_config (execution : nativeApp.Execution) (event : nativeGraph.EventId)
    (who : Bool) :
    (silentWindow execution event who).application.config = execution.application.config := rfl

theorem select_empty (execution : nativeApp.Execution)
    (eligible : Message Bool (WitnessedPacket nativeGraph) → Bool)
    (empty : execution.network.pending = []) :
    nativeApp.uniformInstruction dependencyCondition execution.environmentRecall
      (execution.observeEnvironment nativeApp) (.select eligible) = FinDist.pure .wait := by
  change (MessageNetwork.uniformPending _ execution.network.pending).map _ = _
  rw [empty, MessageNetwork.uniformPending_empty, FinDist.map_pure]
  rfl

def silentWindowTrace (remaining : Nat) (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool)
    (trace : nativeArena.Trace (some ⟨remaining + 3, none, execution⟩))
    (grant : nativeCalendar execution.environmentRecall.length = .application (.grant event))
    (activate : nativeCalendar (execution.environmentRecall.length + 1) = .activate who)
    (select : nativeCalendar (execution.environmentRecall.length + 2) =
      .select (eventProposal event who))
    (empty : execution.network.pending = []) :
    nativeArena.Trace (some ⟨remaining, none, silentWindow execution event who⟩) := by
  let granted := nativeGrant execution event
  let activated := nativeActivate granted who
  let responded := activated.respond nativeApp who ⟨none⟩
  have first : nativeArena.Trace (some ⟨remaining + 2, none, granted⟩) :=
    nativeEnvironmentTrace (remaining + 2) execution granted trace (.application (.grant event))
      (native_schedule execution _ grant) (native_grant_law execution event)
  have activePosition : nativeCalendar granted.environmentRecall.length = .activate who := by
    simpa only [granted, nativeGrant, nativeRecord, List.length_append, List.length_singleton]
      using activate
  have second : nativeArena.Trace (some ⟨remaining + 1, some who, activated⟩) :=
    nativeEnvironmentTrace (remaining + 1) granted activated first (.activate who)
      (native_schedule granted _ activePosition) (native_activate_law granted who)
  have third : nativeArena.Trace (some ⟨remaining + 1, none, responded⟩) :=
    nativeResponseTrace (remaining + 1) activated who second ⟨none⟩ (by
      rw [MessageBounds.menu_mem]
      exact ⟨trivial, rfl⟩)
  have selectPosition : nativeCalendar responded.environmentRecall.length =
      .select (eventProposal event who) := by
    dsimp only [responded]
    rw [nativeApp.respond_environmentRecall]
    simpa only [activated, granted, nativeActivate, nativeGrant, nativeRecord,
      List.length_append, List.length_singleton, Nat.add_assoc] using select
  apply nativeEnvironmentTrace remaining responded (silentWindow execution event who) third .wait
  · rw [native_schedule responded _ selectPosition]
    exact select_empty responded _ empty
  · rw [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
    rfl

def silentFirst (bit : Bool) : nativeApp.Execution :=
  silentWindow (nativeInitialExecution bit) bindingEvent false

def silentSecond (bit : Bool) : nativeApp.Execution :=
  silentWindow (silentFirst bit) dummyEvent false

def silentThird (bit : Bool) : nativeApp.Execution :=
  silentWindow (silentSecond bit) secretEvent false

def silentBob (bit : Bool) : nativeApp.Execution :=
  nativeActivate (nativeGrant (silentThird bit) guessEvent) true

def silentBobTrace (bit : Bool) :
    nativeArena.Trace (some ⟨45, some true, silentBob bit⟩) := by
  have first : nativeArena.Trace (some ⟨53, none, silentFirst bit⟩) :=
    silentWindowTrace 53 (nativeInitialExecution bit) bindingEvent false
      (nativeSetupTrace bit) rfl rfl rfl rfl
  have firstLength : (silentFirst bit).environmentRecall.length = 3 :=
    silentWindow_length _ _ _
  have second : nativeArena.Trace (some ⟨50, none, silentSecond bit⟩) :=
    silentWindowTrace 50 (silentFirst bit) dummyEvent false first
      (by rw [firstLength]; rfl) (by rw [firstLength]; rfl)
      (by rw [firstLength]; rfl) rfl
  have secondLength : (silentSecond bit).environmentRecall.length = 6 := by
    rw [silentSecond, silentWindow_length, firstLength]
  have third : nativeArena.Trace (some ⟨47, none, silentThird bit⟩) :=
    silentWindowTrace 47 (silentSecond bit) secretEvent false second
      (by rw [secondLength]; rfl) (by rw [secondLength]; rfl)
      (by rw [secondLength]; rfl) rfl
  have thirdLength : (silentThird bit).environmentRecall.length = 9 := by
    rw [silentThird, silentWindow_length, secondLength]
  have granted := nativeEnvironmentTrace 46 (silentThird bit)
    (nativeGrant (silentThird bit) guessEvent) third (.application (.grant guessEvent))
      (native_schedule (silentThird bit) (.application (.grant guessEvent))
        (by rw [thirdLength]; rfl)) (native_grant_law _ _)
  exact nativeEnvironmentTrace 45 _ (silentBob bit) granted (.activate true)
    (native_schedule (nativeGrant (silentThird bit) guessEvent) (.activate true) (by
      change nativeCalendar ((silentThird bit).environmentRecall ++ [_]).length = _
      rw [List.length_append, List.length_singleton, thirdLength]
      rfl)) (native_activate_law _ _)

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

end VegasTests.CommunicationServiceOmission
