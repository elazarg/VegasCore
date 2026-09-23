/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Regularity
import Mathlib.Data.Finset.Max

/-! # Stable priority selection

A priority order includes its tie breaking. Inserting a candidate either
selects that candidate or preserves the previous winner, at each fixed order.
Randomizing over orders preserves regularity without requiring unchanged
relative probabilities. No claim about the source of priorities is assumed.
-/

noncomputable section

namespace GameTheory.Math.Probability.PriorityChoice

open Math.Probability

variable {Candidate : Type*}

def choose (priority : LinearOrder Candidate) (candidates : Finset Candidate) :
    Option Candidate :=
  letI := priority
  if nonempty : candidates.Nonempty then some (candidates.min' nonempty) else none

theorem choose_mem (priority : LinearOrder Candidate) (candidates : Finset Candidate)
    (candidate : Candidate) (chosen : choose priority candidates = some candidate) :
    candidate ∈ candidates := by
  let := priority
  unfold choose at chosen
  split at chosen
  · cases Option.some.inj chosen
    exact Finset.min'_mem ..
  · cases chosen

theorem choose_insert [DecidableEq Candidate]
    (priority : LinearOrder Candidate) (candidates : Finset Candidate)
    (fresh : Candidate) :
    choose priority (insert fresh candidates) = choose priority candidates ∨
      choose priority (insert fresh candidates) = some fresh := by
  let := priority
  by_cases nonempty : candidates.Nonempty
  · have inserted := Finset.insert_nonempty fresh candidates
    simp only [choose, dite_eq_left nonempty, dite_eq_left inserted]
    by_cases same : (insert fresh candidates).min' inserted = fresh
    · exact Or.inr (congrArg some same)
    · apply Or.inl
      apply congrArg some
      apply le_antisymm
      · exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.min'_mem _ _))
      · exact Finset.min'_le _ _
          ((Finset.mem_insert.mp (Finset.min'_mem _ _)).resolve_left same)
  · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst candidates
    simp [choose]

def law (priorities : FinDist (LinearOrder Candidate)) (candidates : Finset Candidate) :
    FinDist (Option Candidate) := priorities.map (fun priority => choose priority candidates)

/-- A fixed law over priority orders is regular under candidate insertion. -/
theorem law_regular_insert [DecidableEq Candidate]
    (priorities : FinDist (LinearOrder Candidate)) (candidates : Finset Candidate)
    (fresh : Candidate) :
    (law priorities candidates).RegularAt (law priorities (insert fresh candidates))
      (some fresh) := by
  apply FinDist.regularAt_of_coupling
  intro priority _
  exact choose_insert priority candidates fresh

theorem law_supported (priorities : FinDist (LinearOrder Candidate))
    (candidates : Finset Candidate) (candidate : Candidate)
    (supported : some candidate ∈ (law priorities candidates).support) :
    candidate ∈ candidates := by
  rw [law, FinDist.support_map] at supported
  obtain ⟨priority, _, chosen⟩ := supported
  exact choose_mem priority candidates candidate chosen

theorem law_none_not_supported (priorities : FinDist (LinearOrder Candidate))
    (candidates : Finset Candidate) (nonempty : candidates.Nonempty) :
    none ∉ (law priorities candidates).support := by
  rw [law, FinDist.support_map]
  rintro ⟨priority, _, chosen⟩
  simp only [choose, dite_eq_left nonempty] at chosen
  cases chosen

end GameTheory.Math.Probability.PriorityChoice
