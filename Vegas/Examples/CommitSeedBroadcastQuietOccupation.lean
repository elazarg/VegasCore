/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastRecordedOccupation
import Vegas.Examples.CommitSeedBroadcastFirstLateLaw
import GameTheory.Math.Probability.ExpectationConditioning

/-! # Actual full-input occupation under the original quiet experiment -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

open Classical in
/-- At a specified complete second-response input, the recorded-response
reward is the literal native observation indicator on every control. -/
theorem firstLate_input_reward (owner : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView) (length : past.length = 1)
    (clock : view.application.2.native.clock = 2) (state : app.ProtocolState) :
    secondResponseReward owner (fun input => if input = some (past, view) then 1 else 0) state =
      if app.observe owner state = some (past, view) then 1 else 0 := by
  classical
  cases state with
  | none => simp only [secondResponseReward, ReactiveApplication.observe, reduceCtorEq, ite_false]
  | some current =>
      by_cases active : current.actor = some owner
      · simp only [ReactiveApplication.observe, active, ite_true]
        by_cases same :
            (current.execution.recall owner, current.execution.observe app owner) = (past, view)
        · have recalled := congrArg Prod.fst same
          have observed := congrArg Prod.snd same
          have actualLength : (current.execution.recall owner).length = 1 :=
            (congrArg List.length recalled).trans length
          have actualClock : current.execution.application.current.native.clock = 2 :=
            (congrArg (fun actual : app.PlayerView => actual.application.2.native.clock)
              observed).trans clock
          change (if current.actor = some owner ∧
              (current.execution.recall owner).length = 1 then
            if current.execution.application.current.native.clock = 2 then
              if some (current.execution.recall owner, current.execution.observe app owner) =
                some (past, view) then (1 : ℝ) else 0 else 0 else 0) = _
          rw [ite_eq_left ⟨active, actualLength⟩, ite_eq_left actualClock]
        · change (if current.actor = some owner ∧
              (current.execution.recall owner).length = 1 then
            if current.execution.application.current.native.clock = 2 then
              if some (current.execution.recall owner, current.execution.observe app owner) =
                some (past, view) then (1 : ℝ) else 0 else 0 else 0) = _
          simp only [Option.some.injEq, same, ite_false, ite_self]
      · simp only [secondResponseReward, active, false_and, ite_false,
          ReactiveApplication.observe, reduceCtorEq]

open Classical in
/-- The chance coefficient is exactly the original uniform-command factor.
The complete input includes the player's entire own recall and private view. -/
theorem quiet_fixed_input_mass (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ observer, players observer ((initialCallback observer).recall observer)
      ((initialCallback observer).observe app observer) = PMF.pure ⟨none⟩)
    (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (length : past.length = 1) (clock : view.application.2.native.clock = 2) :
    (((app.occupationControlLaw (family seed) players initial horizon).map
      (app.observe owner)) (some (past, view))).toReal =
      quietFirstLateMass players owner (some (past, view)) seed / horizon := by
  classical
  let value : NativeInput → ℝ := fun input => if input = some (past, view) then 1 else 0
  have bounded : ∀ input, |value input| ≤ 1 := by
    intro input
    dsimp only [value]
    split_ifs <;> norm_num
  have occupied := fixed_firstLate_controlOccupation seed players waited owner value
    (by norm_num : 0 ≤ (1 : ℝ)) bounded
  have observationReward : (fun state => if app.observe owner state = some (past, view)
      then (1 : ℝ) else 0) = secondResponseReward owner value := by
    funext state
    exact (firstLate_input_reward owner past view length clock state).symm
  have occupationAtom :
      (((app.occupationControlLaw (family seed) players initial horizon).map
        (app.observe owner)) (some (past, view))).toReal =
      expect (app.occupationControlLaw (family seed) players initial horizon)
        (secondResponseReward owner value) := by
    rw [toReal_map_apply, ← observationReward]
    apply expect_congr_on_support
    intro state _supported
    by_cases equal : app.observe owner state = some (past, view)
    · rw [ite_eq_left equal, ite_eq_left equal.symm]
    · rw [ite_eq_right equal, ite_eq_right (Ne.symm equal)]
  have terminalAtom : expect (app.runRounds (family seed) players 14 initialExecution)
      (fun final => value (firstLateInput owner final)) =
      quietFirstLateMass players owner (some (past, view)) seed := by
    unfold quietFirstLateMass
    rw [toReal_map_apply]
    apply expect_congr_on_support
    intro final _supported
    dsimp only [value]
    by_cases equal : firstLateInput owner final = some (past, view)
    · rw [ite_eq_left equal, ite_eq_left equal.symm]
    · rw [ite_eq_right equal, ite_eq_right (Ne.symm equal)]
  exact occupationAtom.trans (occupied.trans (congrArg (fun mass : ℝ => mass / horizon)
    terminalAtom))

end Vegas.Examples.CommitSeedBroadcast
