/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPrivacy
import VegasTests.WindowedApplication

/-! # Private snapshots and observable guessed-opening receipts -/

noncomputable section

namespace VegasTests.WindowedPrivacy

open Vegas Interaction Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationEarlyBinding
open VegasTests.WindowedApplication (runtime initial)

abbrev Player := VegasTests.ApplicationEarlyBinding.Player

private def register (state : runtime.application.State) (who : Player) (slot : Nat)
    (value : Bool) : runtime.application.State :=
  { state with application := { state.application with
    base := state.application.base.register who slot ⟨.bool, value⟩ } }

private def bind (state : runtime.application.State) (who : Player) (slot : Nat) :
    runtime.application.State :=
  runtime.application.includePending
    { state with pool := (state.pool.submit who (.binding slot (who, slot))).2 }
    (who, 0)

private def bound (secret : Bool) : runtime.application.State :=
  bind (register (bind (register initial 0 0 secret) 0 0) 1 1 false) 1 1

private def bindingActions (secret : Bool) : List runtime.application.Action :=
  [.privateCommand 0 (.register 0 ⟨.bool, secret⟩),
   .submit 0 (.binding 0 (0, 0)), .include (0, 0),
   .privateCommand 1 (.register 1 ⟨.bool, false⟩),
   .submit 1 (.binding 1 (1, 1)), .include (1, 0)]

/-- Both compared snapshots arise by actual canonical binding traffic in the
generated application, with the first disclosure endpoint active. -/
theorem bindings_reach_private_snapshot (secret : Bool) :
    runtime.application.run (bindingActions secret) initial = FinDist.pure (bound secret) ∧
      (bound secret).application.base.frozen 0 = some ⟨.bool, secret⟩ ∧
      runtime.image.activeAddress? (bound secret).application.base.memory = some 3 := by
  constructor
  · simp only [bindingActions, MessageApplication.run_cons, MessageApplication.run_nil,
      MessageApplication.step, FinDist.pure_bind]
    rfl
  · exact ⟨rfl, rfl⟩

private theorem bound_agrees (first second : Bool) :
    (bound first).application.AgreesFor (1 : Player) (bound second).application := by
  constructor
  · constructor
    · rfl
    · intro slot
      rfl
    · intro field slot haccepted
      change (if field = 1 then some (BindingDisposition.opaque ((1 : Player), 1))
        else if field = 0 then some (.opaque (0, 0)) else none) =
          some (.opaque (1, slot)) at haccepted
      by_cases hfield : field = 1
      · subst field
        rfl
      · by_cases hzero : field = 0
        · subst field
          simp at haccepted
        · simp only [if_neg hfield, if_neg hzero] at haccepted
          cases haccepted
  · rfl

private def probe (secret guess : Bool) : runtime.application.State :=
  { bound secret with pool := ((bound secret).pool.submit 1
      (.conditional 3 (.opening (0, 0) ⟨.bool, guess⟩))).2 }

/-- Trying either guessed bit under one's own identity yields identical full
native observations for the two possible hidden snapshots. -/
theorem opponent_probe_observation (first second guess : Bool) (observer : Player) :
    State.observe runtime.application
        (runtime.application.includePending (probe first guess) (1, 1)) observer =
      State.observe runtime.application
        (runtime.application.includePending (probe second guess) (1, 1)) observer := by
  apply runtime.includePending_observe_eq 1 (probe first guess) (probe second guess)
    (bound_agrees first second) rfl rfl (1, 1)
  intro message hmessage _
  have heq : message = ⟨(1, 1), .conditional 3 (.opening (0, 0) ⟨.bool, guess⟩)⟩ :=
    Option.some.inj hmessage.symm
  rw [heq]
  rfl

/-- The probe is rejected even when it guesses the actual frozen value. -/
theorem opponent_probe_rejected (secret guess : Bool) :
    (runtime.application.includePending (probe secret guess) (1, 1)).receipts =
      [((0, 0), true), ((1, 0), true), ((1, 1), false)] := rfl

end VegasTests.WindowedPrivacy

/-- info: 'VegasTests.WindowedPrivacy.opponent_probe_observation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedPrivacy.opponent_probe_observation
