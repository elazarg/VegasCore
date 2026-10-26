/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.LogReach
import Mathlib.Probability.Distributions.Uniform

/-! # Global trace algebra with infinitely many actual histories

A player can repeat either Boolean action forever at one information state.
The actual History carrier is infinite. The finite-coordinate order, coefficient
and log-reach formulas still hold at every finite prefix; no Bayes-antichain or
sequential-equilibrium interpretation is asserted for this repeated-information game.
-/

noncomputable section

namespace GameTheoryExtensionsTests.UnboundedTracePowers

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

@[reducible] def arena : ExecutionProtocol Unit where
  State := Unit
  Action _ := Bool
  init := ()
  active _ _ := True
  available _ _ := Set.univ
  terminal _ := False
  step _ _ := PMF.pure ()
  progress _ _ := ⟨fun _ => some false, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

@[reducible] def signals : InfoSignals arena where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := Unit
  initInfo _ _ _ := ()
  pushInfo _ _ _ _ _ := ()

@[reducible] def model : InformationModel arena where
  toInfoSignals := signals
  menu _ _ := {choice | ∃ bit, choice = some bit}
  menu_adequate who state trace choice := by
    cases choice <;> simp [LegalOption, arena]

instance (who : Unit) : Fintype (model.InfoState who) := inferInstanceAs (Fintype Unit)
instance (who : Unit) (info : Unit) : Fintype (model.Choice who info) := Fintype.ofFinite _
instance (who : Unit) (info : Unit) : Nonempty (model.Choice who info) :=
  ⟨⟨some false, ⟨false, rfl⟩⟩⟩

def joint : Unit → Option Bool := fun _ => some false

theorem legal : arena.Legal () joint :=
  ⟨by simp, fun _ => ⟨trivial, Set.mem_univ _⟩⟩

def trace : Nat → arena.Trace ()
  | 0 => .start
  | n + 1 => .extend (trace n) joint legal (by simp [arena])

theorem trace_length (n : Nat) : (trace n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [trace, Trace.length, ih]

theorem actual_histories_infinite : Infinite arena.History := by
  apply Infinite.of_injective (fun n : Nat => (⟨(), trace n⟩ : arena.History))
  intro first second same
  have lengths := congrArg (fun history : arena.History => history.trace.length) same
  simpa only [trace_length] using lengths

def order (_ : Unit) (_ : Unit) (_ : model.Choice () ()) : Nat := 1

def coefficient (_ : Unit) (_ : Unit) (_ : model.Choice () ()) : ℝ := 2

theorem coefficient_positive (who : Unit) (info : model.InfoState who)
    (choice : model.Choice who info) : 0 < coefficient who info choice := by norm_num [coefficient]

def profile (who : Unit) (info : model.InfoState who) : PMF (model.Choice who info) :=
  PMF.uniformOfFintype _

theorem profile_full (who : Unit) (info : model.InfoState who) (choice : model.Choice who info) :
    choice ∈ (profile who info).support := PMF.mem_support_uniformOfFintype choice

def choiceEquiv : Bool ≃ model.Choice () () :=
  Equiv.ofBijective (fun bit => ⟨some bit, ⟨bit, rfl⟩⟩) ⟨fun _ _ same =>
    Option.some.inj (congrArg Subtype.val same), fun choice => by
    obtain ⟨bit, same⟩ := choice.property
    exact ⟨bit, Subtype.ext same.symm⟩⟩

theorem profile_atom (who : Unit) (info : model.InfoState who) (choice : model.Choice who info) :
    (profile who info choice).toReal = 1 / 2 := by
  cases who
  cases info
  have card : Fintype.card (model.Choice () ()) = 2 := by
    rw [← Fintype.card_congr choiceEquiv]
    decide
  change (PMF.uniformOfFintype _ choice).toReal = _
  rw [PMF.uniformOfFintype_apply, card]
  norm_num

theorem prefix_order (n : Nat) : model.powerHistoryOrder order (trace n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trace, powerHistoryOrder, order, ih]

theorem prefix_nature (n : Nat) : historyNatureLog (trace n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [trace, historyNatureLog, arena, ih]

/-- The natural count formula remains applicable without finite actual History. -/
theorem prefix_count (n : Nat) :
    (∑ coordinate, model.historyActionCount (trace n) coordinate) = n := by
  have formula := model.powerHistoryOrder_eq_sum order (trace n)
  simpa only [prefix_order, order, mul_one] using formula.symm

theorem prefix_count_real (n : Nat) :
    (∑ coordinate, (model.historyActionCount (trace n) coordinate : ℝ)) = n := by
  have formula := model.powerHistoryOrder_cast_eq_sum (R := ℝ) order (trace n)
  simpa only [prefix_order, order, Nat.cast_one, mul_one] using formula.symm

/-- The generic semiring count increment also covers each unbounded prefix. -/
theorem prefix_count_increment {R : Type*} [Semiring R]
    (value : model.BehavioralCoordinate → R) (n : Nat) :
    (∑ coordinate, (model.historyActionCount (trace (n + 1)) coordinate : R) *
      value coordinate) =
      (∑ coordinate, (model.historyActionCount (trace n) coordinate : R) * value coordinate) +
        value ⟨(), model.infoOf () (trace n),
          model.choicesOfLegal (trace n) ⟨joint, legal⟩ ()⟩ := by
  simpa only [trace, Fintype.sum_unique] using
    model.historyActionCount_sum_extend value (trace n) joint legal (by simp [arena])

/-- Positive action coefficients retain their actual multiplicity at all depths. -/
theorem prefix_coefficient_log (n : Nat) :
    Real.log (model.powerHistoryCoefficient coefficient (trace n)) = (n : ℝ) * Real.log 2 := by
  have formula := model.powerHistoryCoefficient_log_eq coefficient coefficient_positive (trace n)
  simpa only [coefficient, prefix_nature, zero_add, ← Finset.sum_mul, prefix_count_real]
    using formula

/-- The existing canonical evaluator has the computed log reach at every depth. -/
theorem prefix_reach_log (n : Nat) :
    Real.log ((model.historyReachWeight profile ⟨(), trace n⟩).toReal) =
      (n : ℝ) * Real.log (1 / 2) := by
  have formula := model.historyReachWeight_log_eq profile profile_full (trace n)
  simp_rw [profile_atom] at formula
  simpa only [prefix_nature, zero_add, ← Finset.sum_mul, prefix_count_real] using formula

/-- Exact log odds of arbitrary prefixes do not require a finite History carrier. -/
theorem prefix_reach_log_ratio (first second : Nat) :
    -Real.log ((model.historyReachWeight profile ⟨(), trace first⟩).toReal /
      (model.historyReachWeight profile ⟨(), trace second⟩).toReal) =
        ((first : ℝ) - second) * (-Real.log (1 / 2)) := by
  have formula := model.historyLogRate_difference profile profile_full
    ⟨(), trace first⟩ ⟨(), trace second⟩
  simp_rw [profile_atom] at formula
  simp only [prefix_nature, sub_self, zero_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.sum_mul, prefix_count_real] at formula
  exact formula.symm.trans (by ring)

end GameTheoryExtensionsTests.UnboundedTracePowers
