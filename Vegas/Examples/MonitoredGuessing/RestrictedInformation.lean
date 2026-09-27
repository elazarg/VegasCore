/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedExecution

/-! # Source decision inputs at the restricted native checkpoints

Bob has one input for both hidden initial bits. Alice's input determines exactly
the source bit and Bob's publication choice. The menu equations certify both
source actions, including silence, at these concrete inputs. Classification of
all restricted histories is a separate obligation.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def aliceInput (bit guess : Bool) : nativeApp.Info :=
  some ((beforeAlice bit guess).recall alice, (beforeAlice bit guess).observe nativeApp alice)

def decodeAliceInput : nativeApp.Info → Bool × Bool
  | none => (false, false)
  | some (_, view) =>
      (observedAliceBit view,
        ((bobPublicationRef.get? view.application.observation.store).getD .failure).isSuccess)

theorem decode_alice_input (bit guess : Bool) :
    decodeAliceInput (aliceInput bit guess) = (bit, guess) := by
  change (observedAliceBit ((beforeAlice bit guess).observe nativeApp alice), _) = _
  rw [native_observed_alice_bit bit _ (before_alice_fixed bit guess)]
  apply congrArg (Prod.mk bit)
  change ((bobPublicationRef.get?
    (nativeGraph.playerStore alice (beforeAlice bit guess).application.config.store)).getD
      .failure).isSuccess = guess
  rw [EventGraph.FieldRef.get?_playerStore bobPublicationRef alice _ (by trivial)]
  have stored : bobPublicationRef.get? (beforeAlice bit guess).application.config.store =
    some (guessResult guess) := after_bob_stored bit guess
  rw [stored]
  cases guess <;> rfl

theorem alice_input_eq_iff (bit guess other decision : Bool) :
    aliceInput bit guess = aliceInput other decision ↔ bit = other ∧ guess = decision := by
  constructor
  · intro same
    have decoded := congrArg decodeAliceInput same
    rw [decode_alice_input, decode_alice_input] at decoded
    exact Prod.mk.inj decoded
  · rintro ⟨rfl, rfl⟩
    rfl

theorem bob_input (bit : Bool) :
    some ((quietBob bit).recall bob, (quietBob bit).observe nativeApp bob) = quietBobInfo :=
  quiet_bob_info bit

open Classical in
theorem bob_actions (bit : Bool) :
    restrictedMenu.actions bob ((quietBob bit).recall bob) ((quietBob bit).observe nativeApp bob) =
      {nativeSilent, nativeOpeningAction bobPublication bobHandle true} := by
  classical
  have notWatcher : bob ≠ watcher := by decide
  simp only [restrictedMenu, notWatcher, ↓reduceIte]
  rw [ordinaryActions, ite_eq_left ⟨rfl, rfl⟩, quiet_bob_opening]

open Classical in
theorem alice_actions (bit guess : Bool) :
    restrictedMenu.actions alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) =
      {nativeSilent, nativeOpeningAction alicePublication aliceHandle bit} := by
  classical
  have notWatcher : alice ≠ watcher := by decide
  have notBob : alice ≠ bob := by decide
  simp only [restrictedMenu, notWatcher, ↓reduceIte]
  rw [ordinaryActions, ite_eq_right (fun matching => notBob matching.1),
    ite_eq_left ⟨rfl, rfl⟩, before_alice_opening]

theorem bob_choice_available (bit guess : Bool) :
    choiceAction bobPublication bobHandle true guess ∈
      restrictedMenu.actions bob ((quietBob bit).recall bob)
        ((quietBob bit).observe nativeApp bob) := by
  classical
  rw [bob_actions]
  cases guess <;> simp [choiceAction]

theorem alice_choice_available (bit guess disclose : Bool) :
    choiceAction alicePublication aliceHandle bit disclose ∈
      restrictedMenu.actions alice ((beforeAlice bit guess).recall alice)
        ((beforeAlice bit guess).observe nativeApp alice) := by
  classical
  rw [alice_actions]
  cases disclose <;> simp [choiceAction]

theorem choiceAction_injective (event : nativeGraph.EventId) (handle : Handle nativeGraph)
    (value : Bool) : Function.Injective (choiceAction event handle value) := by
  intro first second same
  cases first <;> cases second <;> cases same <;> rfl

end Vegas.Examples.MonitoredGuessing.Restricted
