/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativePrelude
import Interaction.ReactiveMenuPolicy

/-! # Prescribed responses and the quiet decision observation

The actions below are elements of the complete raw response menu. Their
availability does not remove any alternative raw response.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def nativeSilent : nativeApp.Action := ⟨none⟩

def nativeOpeningAction (event : nativeGraph.EventId) (handle : Handle nativeGraph)
    (bit : Bool) : nativeApp.Action :=
  ⟨some (.submit ⟨⟨.opening event handle ⟨.bool, bit⟩, none⟩,
    .owned ⟨handle, ⟨.bool, bit⟩⟩⟩)⟩

def nativeGuessAction (guess : Bool) : nativeApp.Action :=
  if guess then nativeOpeningAction bobPublication bobHandle true
  else ⟨some (.submit ⟨⟨.withhold bobPublication, none⟩, .none⟩)⟩

def observedAliceBit (view : nativeApp.PlayerView) : Bool :=
  match view.application.candidates (.initial aliceInput) with
  | .openable raw => (raw.as? .bool).getD false
  | _ => false

def nativeAliceResponse (view : nativeApp.PlayerView) : nativeApp.Action :=
  if view.application.publicView.serviceGrant = some alicePublication then
    nativeOpeningAction alicePublication aliceHandle (observedAliceBit view)
  else nativeSilent

def nativeWatcherResponse (view : nativeApp.PlayerView) : nativeApp.Action :=
  match view.messages.leaked.find? (fun message => message.sender = alice) with
  | none => nativeSilent
  | some message => ⟨some (.replay message.id)⟩

theorem native_silent_available (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) : nativeSilent ∈ nativeMenu.actions who past view := by
  change nativeSilent ∈ (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions who past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  trivial

theorem native_opening_available (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (event : nativeGraph.EventId) (handle : Handle nativeGraph)
    (allowed : nativeBounds.AllowsHandle handle) (bit : Bool) :
    nativeOpeningAction event handle bit ∈ nativeMenu.actions who past view := by
  change nativeOpeningAction event handle bit ∈
    (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions who past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.opening event handle ⟨.bool, bit⟩, none⟩,
    .owned ⟨handle, ⟨.bool, bit⟩⟩⟩ : WitnessedSubmission nativeGraph) ∈ _
  rw [MessageBounds.submissions_mem]
  have value : (⟨.bool, bit⟩ : Raw simpleExpr) ∈ nativeBounds.values := by cases bit <;> decide
  exact ⟨⟨⟨allowed, value⟩, trivial⟩, allowed, value⟩

theorem native_guess_available (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) (guess : Bool) :
    nativeGuessAction guess ∈ nativeMenu.actions bob past view := by
  cases guess with
  | false =>
      change nativeGuessAction false ∈
        (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions bob past view
      rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
      change (⟨⟨.withhold bobPublication, none⟩, .none⟩ : WitnessedSubmission nativeGraph) ∈ _
      rw [MessageBounds.submissions_mem]
      exact ⟨⟨trivial, trivial⟩, trivial⟩
  | true => exact native_opening_available bob past view bobPublication bobHandle trivial true

theorem native_alice_available (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) :
    nativeAliceResponse view ∈ nativeMenu.actions alice past view := by
  unfold nativeAliceResponse
  split
  · exact native_opening_available alice past view alicePublication aliceHandle trivial _
  · exact native_silent_available alice past view

theorem native_watcher_available (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) :
    nativeWatcherResponse view ∈ nativeMenu.actions watcher past view := by
  unfold nativeWatcherResponse
  split
  · exact native_silent_available watcher past view
  · rename_i message found
    change (⟨some (.replay message.id)⟩ : nativeApp.Action) ∈
      (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions watcher past view
    rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    refine ⟨message, ?_, rfl⟩
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_of_find?_eq_some found))

def nativeAlicePolicy : nativeApp.Policy := fun _ view => FinDist.pure (nativeAliceResponse view)
def nativeWatcherPolicy : nativeApp.Policy :=
  fun _ view => FinDist.pure (nativeWatcherResponse view)
def nativeGuessPolicy (guesses : FinDist Bool) : nativeApp.Policy :=
  fun _ _ => guesses.map nativeGuessAction

theorem native_alice_admissible : nativeMenu.Admissible nativeInitialLaw nativeHorizon
    nativeScheduler alice nativeAlicePolicy := by
  intro control _ _ action supported
  cases FinDist.mem_support_pure.mp supported
  exact native_alice_available _ _

theorem native_watcher_admissible : nativeMenu.Admissible nativeInitialLaw nativeHorizon
    nativeScheduler watcher nativeWatcherPolicy := by
  intro control _ _ action supported
  cases FinDist.mem_support_pure.mp supported
  exact native_watcher_available _ _

def nativeAliceBehavior : nativeModel.BehavioralPolicy alice :=
  nativeMenu.restrictPolicy nativeInitialLaw nativeHorizon nativeScheduler alice
    nativeAlicePolicy native_alice_admissible

def nativeWatcherBehavior : nativeModel.BehavioralPolicy watcher :=
  nativeMenu.restrictPolicy nativeInitialLaw nativeHorizon nativeScheduler watcher
    nativeWatcherPolicy native_watcher_admissible

/-- The actual execution after silent ambient responses and the first grant. -/
def quietBob (bit : Bool) : nativeApp.Execution :=
  let previous := watcherRespond bit nativeSilent ∅ nativeSilent
  let afterWire : nativeApp.Execution := { previous with
    environmentRecall := previous.environmentRecall ++
      [⟨previous.observeEnvironment nativeApp, .wait⟩] }
  let granted : nativeApp.Execution := { afterWire with
    application := { afterWire.application with serviceGrant := some bobPublication }
    environmentRecall := afterWire.environmentRecall ++
      [⟨afterWire.observeEnvironment nativeApp, .application (.grant bobPublication)⟩] }
  { granted with environmentRecall := granted.environmentRecall ++
    [⟨granted.observeEnvironment nativeApp, .activate bob⟩] }

def quietBobInfo : nativeApp.Info := some ([], (quietBob false).observe nativeApp bob)

theorem quiet_bob_observation (bit : Bool) :
    (quietBob bit).observe nativeApp bob = (quietBob false).observe nativeApp bob := by
  cases bit with
  | false => rfl
  | true =>
      unfold ReactiveApplication.Execution.observe
      congr 1
      change (⟨bob, _, nativeGraph.playerObserve bob _, _⟩ : ReactivePlayerView nativeGraph) = _
      congr 1
      · unfold State.publicView
        congr 1
        apply EventGraph.PublicObservation.ext
        · rfl
        · apply nativeGraph.publicStore_congr
          intro field visible
          cases field with
          | inl input =>
              fin_cases input <;> exact False.elim visible
          | inr event => fin_cases event <;> rfl
      · apply EventGraph.PlayerObservation.ext
        · rfl
        · apply nativeGraph.playerStore_congr
          intro field visible
          cases field with
          | inl input =>
              fin_cases input
              · exact False.elim (by
                  change (0 : Player) = 1 at visible
                  cases visible)
              · rfl
          | inr event => fin_cases event <;> rfl
        · rfl
      · funext slot
        cases slot with
        | initial input => fin_cases input <;> rfl
        | prepared serial => rfl

theorem quiet_bob_recall (bit : Bool) : (quietBob bit).recall bob = [] := rfl

theorem quiet_bob_info (bit : Bool) :
    some ((quietBob bit).recall bob, (quietBob bit).observe nativeApp bob) = quietBobInfo := by
  rw [quiet_bob_recall, quiet_bob_observation]
  rfl

end VegasTests.MonitoredGuessing
