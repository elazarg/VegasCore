/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationFibre

/-! # Bob's two concrete response packets -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeGuessBinding : EventGraph.FieldRef nativeGraph.layout (.binding true .bool) :=
  ⟨.inl guessInput, rfl⟩

theorem native_guess_node : nodeView nativeGraph guessEvent =
    .resolve true .bool nativeGuessBinding [] (by rfl) (by rfl) := rfl

theorem native_secret_ready (bit : Bool) :
    (nativeSecretPublished bit).config.cut.Ready guessEvent := by
  simp only [nativeSecretPublished_eq, nativeSecretState, nativeDummyPublished_eq,
    nativeDummyState, nativeBound_eq]
  cases bit <;> decide

theorem native_secret_clock (bit : Bool) : (nativeSecretPublished bit).clock = 0 := by
  simp only [nativeSecretPublished_eq, nativeSecretState, State.complete,
    nativeDummyPublished_eq, nativeDummyState, native_bound_clock]

theorem native_secret_timely (bit : Bool) :
    (nativeSecretPublished bit).WithinDeadline nativeRuntime guessEvent := by
  have ready := native_secret_ready bit
  rw [nativeSecretPublished_eq] at ready ⊢
  have actor : nativeGraph.actor? guessEvent = some true := rfl
  have clock : (nativeDummyPublished bit).clock = 0 := by
    rw [nativeDummyPublished_eq]
    exact native_bound_clock bit
  change (match State.refreshActivated (nativeSecretState bit).config
      (nativeDummyPublished bit).clock (nativeDummyPublished bit).activatedAt guessEvent with
    | none => False | some entered => (nativeDummyPublished bit).clock - entered < 10)
  rw [State.refreshActivated, dite_eq_left ready, actor, clock]
  cases (nativeDummyPublished bit).activatedAt guessEvent <;> simp

theorem native_secret_associated (bit : Bool) :
    (nativeSecretPublished bit).accepted nativeGuessBinding.field =
      some (true, .initial guessInput) := by
  simp only [nativeSecretPublished_eq, nativeSecretState, State.complete,
    nativeDummyPublished_eq, nativeDummyState, nativeBound_eq]
  rfl

theorem native_secret_guess_candidate (bit : Bool) :
    (nativeSecretPublished bit).candidates.lookup (true, .initial guessInput) =
      .openable ⟨.bool, true⟩ := by
  simp only [nativeSecretPublished_eq, nativeSecretState, State.complete,
    nativeDummyPublished_eq, nativeDummyState, nativeBound_eq]
  cases bit <;> rfl

theorem native_secret_guess_stored (bit : Bool) :
    nativeGuessBinding.get? (nativeSecretPublished bit).config.store = some (.success true) := by
  simp only [nativeSecretPublished_eq, nativeSecretState, State.complete,
    nativeDummyPublished_eq, nativeDummyState, nativeBound_eq]
  rfl

theorem native_secret_remembered (bit : Bool) :
    (nativeSecretPublished bit).remembered guessEvent = none := by
  simp only [nativeSecretPublished_eq, nativeSecretState, State.complete,
    nativeDummyPublished_eq, nativeDummyState, nativeBound_eq]
  rfl

def nativeGuessSubmission (guess : Bool) : WitnessedSubmission nativeGraph :=
  ⟨⟨if guess then .opening guessEvent (true, .initial guessInput) ⟨.bool, true⟩
    else .withhold guessEvent, none⟩, .none⟩

def nativeGuessState (bit guess : Bool) : State nativeGraph :=
  (nativeSecretPublished bit).complete guessEvent (native_secret_ready bit) guess
    (if guess then .success true else .failure)

theorem native_guess_law (bit guess : Bool) (serial : Nat) :
    nativeSubmit (nativeSecretPublished bit) true serial (nativeGuessSubmission guess).call =
      some (nativeGuessState bit guess) := by
  unfold nativeSubmit
  rw [handle_submitStep]
  cases guess with
  | false =>
      exact handle_withhold_unremembered_eq nativeRuntime (nativeSecretPublished bit)
        (true, serial) guessEvent true .bool nativeGuessBinding [] rfl rfl native_guess_node
        (native_secret_ready bit) (native_secret_timely bit) rfl (native_secret_remembered bit)
  | true =>
      apply handle_opening_eq nativeRuntime (nativeSecretPublished bit) (true, serial) guessEvent
        (true, .initial guessInput) true .bool nativeGuessBinding [] rfl rfl native_guess_node
        (native_secret_ready bit) (native_secret_timely bit) rfl rfl
        (native_secret_associated bit) true (native_secret_guess_candidate bit)
        (native_secret_guess_stored bit) (.success true)
      simp [EventGraph.EventCode.resolveOutput?, native_secret_guess_stored,
        EventGraph.GuardCheck.allAccepted?]

theorem native_guess_grant (bit guess : Bool) (serial : Nat) (grant : Option nativeGraph.EventId) :
    nativeSubmit { nativeSecretPublished bit with serviceGrant := grant } true serial
      (nativeGuessSubmission guess).call =
        some { nativeGuessState bit guess with serviceGrant := grant } := by
  have accepted := native_guess_law bit guess serial
  unfold nativeSubmit at accepted ⊢
  rw [handle_submitStep] at accepted ⊢
  cases guess <;>
    change handle nativeRuntime { nativeSecretPublished bit with serviceGrant := grant }
      ⟨(true, serial), _⟩ = _
  all_goals change handle nativeRuntime (nativeSecretPublished bit) ⟨(true, serial), _⟩ = _
    at accepted
  all_goals rw [handle_serviceGrant_update, accepted]; rfl

theorem native_guess_available (guess : Bool) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) :
    (⟨some (.submit (nativeGuessSubmission guess))⟩ : nativeApp.Action) ∈
      nativeMenu.actions true past view := by
  cases guess
  · exact native_withhold_available _ _ _ _
  · exact native_opening_available _ _ _ _ _ _ trivial

def nativeGuess (state : State nativeGraph) : Bool :=
  (state.config.store (.inr guessEvent)).getD .failure |>.isSuccess

theorem native_guess_result (bit guess : Bool) : nativeGuess (nativeGuessState bit guess) = guess :=
  by cases guess <;> rfl

end VegasTests.SequentialValidation
