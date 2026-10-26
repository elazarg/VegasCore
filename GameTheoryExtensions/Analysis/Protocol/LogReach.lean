/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.FiniteTraceCoordinates

/-! # Global coordinate sums without finite-history assumptions

When the entire behavioral coordinate carrier is finite, the factual trace
cover can be the full coordinate set. These global formulas therefore apply to
arbitrary finite prefixes even when the total legal History carrier is infinite.
The trace induction is shared with the fixed-cover and realized-coordinate APIs.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  [∀ who, Fintype (M.InfoState who)] [∀ who info, Fintype (M.Choice who info)]

private theorem sum_univ_coordinates {R : Type*} [AddCommMonoid R]
    (value : M.BehavioralCoordinate → R) :
    (∑ coordinate : (Finset.univ : Finset M.BehavioralCoordinate), value coordinate.1) =
      ∑ coordinate, value coordinate :=
  (Finset.sum_subtype Finset.univ (fun _ => Iff.rfl) value).symm

theorem historyActionCount_sum_extend {R : Type*} [Semiring R]
    (value : M.BehavioralCoordinate → R)
    {source target : E.State} (prior : E.Trace source)
    (joint : ∀ who, Option (E.Action who)) (legal : E.Legal source joint)
    (realized : target ∈ (E.step source ⟨joint, legal⟩).support) :
    (∑ coordinate, (M.historyActionCount (prior.extend joint legal realized) coordinate : R) *
      value coordinate) =
      (∑ coordinate, (M.historyActionCount prior coordinate : R) * value coordinate) +
        ∑ who, value ⟨who, M.infoOf who prior, M.choicesOfLegal prior ⟨joint, legal⟩ who⟩ := by
  have formula := M.historyActionCount_sum_extend_cover Finset.univ
    (fun coordinate => value coordinate.1) prior joint legal realized (Finset.subset_univ _)
  rw [M.sum_univ_coordinates (fun coordinate =>
      (M.historyActionCount (prior.extend joint legal realized) coordinate : R) * value coordinate),
    M.sum_univ_coordinates (fun coordinate =>
      (M.historyActionCount prior coordinate : R) * value coordinate)] at formula
  exact formula

theorem powerHistoryOrder_eq_sum (order : ∀ who info, M.Choice who info → Nat)
    {state : E.State} (trace : E.Trace state) :
    M.powerHistoryOrder order trace = ∑ coordinate,
      M.historyActionCount trace coordinate * order coordinate.1 coordinate.2.1 coordinate.2.2 := by
  have formula := M.powerHistoryOrder_eq_sum_cover Finset.univ order trace (Finset.subset_univ _)
  rw [M.sum_univ_coordinates (fun coordinate => M.historyActionCount trace coordinate *
    order coordinate.1 coordinate.2.1 coordinate.2.2)] at formula
  exact formula

theorem powerHistoryOrder_cast_eq_sum {R : Type*} [Semiring R]
    (order : ∀ who info, M.Choice who info → Nat) {state : E.State} (trace : E.Trace state) :
    (M.powerHistoryOrder order trace : R) = ∑ coordinate,
      (M.historyActionCount trace coordinate : R) *
        (order coordinate.1 coordinate.2.1 coordinate.2.2 : R) := by
  have formula := M.powerHistoryOrder_cast_eq_sum_cover (R := R) Finset.univ order trace
    (Finset.subset_univ _)
  rw [M.sum_univ_coordinates (fun coordinate => (M.historyActionCount trace coordinate : R) *
    (order coordinate.1 coordinate.2.1 coordinate.2.2 : R))] at formula
  exact formula

theorem powerHistoryCoefficient_log_eq
    (coefficient : ∀ who info, M.Choice who info → ℝ)
    (positive : ∀ who info choice, 0 < coefficient who info choice)
    {state : E.State} (trace : E.Trace state) :
    Real.log (M.powerHistoryCoefficient coefficient trace) =
      historyNatureLog trace + ∑ coordinate, (M.historyActionCount trace coordinate : ℝ) *
        Real.log (coefficient coordinate.1 coordinate.2.1 coordinate.2.2) := by
  have formula := M.powerHistoryCoefficient_log_eq_cover Finset.univ coefficient positive trace
    (Finset.subset_univ _)
  rw [M.sum_univ_coordinates (fun coordinate => (M.historyActionCount trace coordinate : ℝ) *
    Real.log (coefficient coordinate.1 coordinate.2.1 coordinate.2.2))] at formula
  exact formula

theorem historyReachWeight_log_eq (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    {state : E.State} (trace : E.Trace state) :
    Real.log ((M.historyReachWeight profile ⟨state, trace⟩).toReal) =
      historyNatureLog trace + ∑ coordinate,
        (M.historyActionCount trace coordinate : ℝ) *
          Real.log ((profile coordinate.1 coordinate.2.1 coordinate.2.2).toReal) := by
  have formula := M.historyReachWeight_log_eq_cover Finset.univ profile full trace
    (Finset.subset_univ _)
  rw [M.sum_univ_coordinates (fun coordinate => (M.historyActionCount trace coordinate : ℝ) *
    Real.log ((profile coordinate.1 coordinate.2.1 coordinate.2.2).toReal))] at formula
  exact formula

theorem historyLogRate_difference (profile : ∀ who, M.BehavioralPolicy who)
    (full : ∀ who info choice, choice ∈ (profile who info).support)
    (history reference : E.History) :
    (∑ coordinate, ((M.historyActionCount history.trace coordinate : ℝ) -
      (M.historyActionCount reference.trace coordinate : ℝ)) *
        (-Real.log ((profile coordinate.1 coordinate.2.1 coordinate.2.2).toReal))) =
      historyNatureLog history.trace - historyNatureLog reference.trace -
        Real.log ((M.historyReachWeight profile history).toReal /
          (M.historyReachWeight profile reference).toReal) := by
  have formula := M.historyLogRate_difference_cover Finset.univ profile full history reference
    (Finset.subset_univ _) (Finset.subset_univ _)
  rw [M.sum_univ_coordinates (fun coordinate =>
    ((M.historyActionCount history.trace coordinate : ℝ) -
      (M.historyActionCount reference.trace coordinate : ℝ)) *
        (-Real.log ((profile coordinate.1 coordinate.2.1 coordinate.2.2).toReal)))] at formula
  exact formula

end GameTheory.Protocol.InformationModel
