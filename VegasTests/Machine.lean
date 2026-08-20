/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Administrative
import Vegas.Machine.Instrumentation

namespace VegasTests.Machine

open GameTheory.Math.Probability
open Vegas.Machine

inductive Advance : Nat → Type
  | next {state : Nat} : Advance state

noncomputable def counter : System where
  State := Nat
  Command := Advance
  init := 0
  step := fun state _ => FinDist.pure (state + 1)
  terminal := fun state => state = 2

inductive Padding : Bool → Type
  | flip {state : Bool} : Padding state

noncomputable def padding : AdministrativeLayer counter where
  Metadata := Bool
  initial := false
  Command := Padding
  step := fun metadata _ =>
    FinDist.pure (!metadata)

noncomputable example : Refinement counter padding.lower :=
  padding.refinement

noncomputable example : padding.refinement.PreservesTerminal :=
  padding.preservesTerminal

example :
    (padding.lower.step ((0 : Nat), false)
      (.semantic Advance.next)).map padding.refinement.projectState =
      counter.step (0 : Nat) Advance.next := by
  exact padding.refinement.step_eq ((0 : Nat), false) (.semantic Advance.next)

example :
    (padding.lower.step ((0 : Nat), false)
      (.administrative Padding.flip)).map padding.refinement.projectState =
      FinDist.pure (0 : Nat) := by
  exact padding.refinement.step_eq_pure_of_administrative
    ((0 : Nat), false) (.administrative Padding.flip) rfl

noncomputable def counterLog : Instrumentation counter :=
  Instrumentation.executionLog counter

noncomputable example : Refinement counter counterLog.lower :=
  counterLog.refinement

example : counterLog.refinement.PreservesTerminal :=
  counterLog.preservesTerminal

example :
    counterLog.lower.step ((0 : Nat), []) Advance.next =
      (counter.step (0 : Nat) Advance.next).map fun next =>
        (next,
          [({ prior := (0 : Nat), command := Advance.next, next := next } :
            Instrumentation.StepRecord counter)]) := by
  exact Instrumentation.executionLog_step counter (0 : Nat) [] Advance.next

end VegasTests.Machine
