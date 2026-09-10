/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnedPrivacy
import VegasTests.WindowedApplication

/-! # Foreign opening privacy at a focal-owned active instruction -/

noncomputable section

namespace VegasTests.WindowedOwnedPrivacy

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
  bind (register (bind (register initial 0 0 false) 0 0) 1 1 secret) 1 1

private def bindingActions (secret : Bool) : List runtime.application.Action :=
  [.privateCommand 0 (.register 0 ⟨.bool, false⟩),
   .submit 0 (.binding 0 (0, 0)), .include (0, 0),
   .privateCommand 1 (.register 1 ⟨.bool, secret⟩),
   .submit 1 (.binding 1 (1, 1)), .include (1, 0)]

/-- Both compared snapshots are reached by actual generated binding traffic,
with the focal-owned first conditional active. -/
theorem bindings_reach_private_snapshot (secret : Bool) :
    runtime.application.run (bindingActions secret) initial = FinDist.pure (bound secret) ∧
      (bound secret).application.base.frozen 1 = some ⟨.bool, secret⟩ ∧
      runtime.image.activeAddress? (bound secret).application.base.memory = some 3 := by
  constructor
  · simp only [bindingActions, MessageApplication.run_cons, MessageApplication.run_nil,
      MessageApplication.step, FinDist.pure_bind]
    rfl
  · exact ⟨rfl, rfl⟩

private def probe (secret guess : Bool) : runtime.application.State :=
  { bound secret with pool := ((bound secret).pool.submit 1
      (.conditional 3 (.opening (0, 0) ⟨.bool, guess⟩))).2 }

private def conditionalCode :=
  firstConditionalSite.code source.fresh compilerInitial 0 10

private theorem lookup_code :
    runtime.image.lookup 3 = some (.conditional conditionalCode) := by
  rfl

private theorem bound_agrees (first second : Bool) :
    (bound first).application.AgreesFor (0 : Player) (bound second).application := by
  constructor
  · constructor
    · rfl
    · intro slot
      rfl
    · intro field slot haccepted
      change (if field = 1 then some (BindingDisposition.opaque ((1 : Player), 1))
        else if field = 0 then some (.opaque (0, 0)) else none) =
          some (.opaque (0, slot)) at haccepted
      by_cases hfield : field = 1
      · subst field
        simp at haccepted
      · by_cases hzero : field = 0
        · subst field
          rfl
        · simp only [if_neg hfield, if_neg hzero] at haccepted
          cases haccepted
  · rfl

/-- A foreign opening aimed at the focal-owned conditional is rejected without
revealing the other owner's different frozen snapshot. -/
theorem foreign_opening_agrees (first second guess : Bool) :
    let left := probe first guess
    let right := probe second guess
    let nextLeft := runtime.application.includePending left (1, 1)
    let nextRight := runtime.application.includePending right (1, 1)
    nextLeft.application.AgreesFor (0 : Player) nextRight.application ∧
      nextLeft.pool = nextRight.pool ∧ nextLeft.receipts = nextRight.receipts := by
  apply runtime.includePending_agrees_of_active_submitter 0
    (probe first guess) (probe second guess) (bound_agrees first second) rfl rfl
    ⟨3, 0⟩ (.conditional conditionalCode)
  · rfl
  · rfl
  · rfl
  · exact lookup_code
  · rfl

theorem foreign_opening_is_rejected (secret guess : Bool) :
    (runtime.application.includePending (probe secret guess) (1, 1)).receipts =
      [((0, 0), true), ((1, 0), true), ((1, 1), false)] := by
  rfl

end VegasTests.WindowedOwnedPrivacy
