/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.PendingChoice
import GameTheoryExtensions.Math.Probability.Regularity

/-! # Optimal proposals under regular selection

`none` in the selection law denotes the fresh candidate, while `some a`
denotes a retained action. Selection is independent of the fresh action's
meaning. A response may submit an action or remain silent. This local game
fixes its continuation kernel; it is not a native SPE certificate.
-/

noncomputable section

namespace GameTheory.PendingChoice

open Math.Probability

variable {Action Outcome : Type*}

structure RegularSelection (Action : Type*) where
  retained : FinDist Action
  selection : FinDist (Option Action)
  regular : (retained.map some).RegularAt selection none

namespace RegularSelection

/-- Decode a regular insertion. The fresh candidate has no old occurrence;
retained candidates may decode to the same source action. -/
def ofInsertion {Candidate : Type*} [DecidableEq Candidate]
    (before after : FinDist Candidate) (fresh : Candidate)
    (absent : fresh ∉ before.support) (regular : before.RegularAt after fresh)
    (decode : Candidate → Action) : RegularSelection Action where
  retained := before.map decode
  selection := after.map fun candidate =>
    if candidate = fresh then none else some (decode candidate)
  regular := by
    have mapped := regular.map
      (fun candidate => if candidate = fresh then none else some (decode candidate))
    have old : before.map (fun candidate =>
        if candidate = fresh then none else some (decode candidate)) =
          (before.map decode).map some := by
      rw [FinDist.map_comp]
      apply FinDist.map_congr_of_eq_on_support
      intro candidate member
      have different : candidate ≠ fresh := fun same => absent (same ▸ member)
      simp only [different, ↓reduceIte, Function.comp_def]
    simpa only [old, ↓reduceIte] using mapped

def includeLaw (rule : RegularSelection Action) : Option Action → FinDist Action
  | none => rule.retained
  | some action => rule.selection.map (fun selected => selected.getD action)

def responseLaw (rule : RegularSelection Action) (responses : FinDist (Option Action)) :
    FinDist Action := responses.bind rule.includeLaw

/-- Decoding a proposal substitutes the new source action at its fresh identity. -/
theorem ofInsertion_submit {Candidate : Type*} [DecidableEq Candidate]
    (before after : FinDist Candidate) (fresh : Candidate)
    (absent : fresh ∉ before.support) (regular : before.RegularAt after fresh)
    (decode : Candidate → Action) (action : Action) :
    (ofInsertion before after fresh absent regular decode).includeLaw (some action) =
      after.map (fun candidate => if candidate = fresh then action else decode candidate) := by
  rw [includeLaw, ofInsertion, FinDist.map_comp]
  apply FinDist.map_congr_of_eq_on_support
  intro candidate _
  by_cases same : candidate = fresh <;> simp [same]

/-- Averaging the submitted action commutes with the independent selection. -/
theorem submitted_value (rule : RegularSelection Action) (law : FinDist Action)
    (value : Action → ℝ) :
    (rule.responseLaw (law.map some)).expect value =
      rule.selection.expect (fun selected => selected.elim (law.expect value) value) := by
  simp only [responseLaw, FinDist.expect_bind, FinDist.expect_map, includeLaw]
  rw [FinDist.expect_comm]
  apply FinDist.expect_congr
  intro selected _
  cases selected <;> simp

/-- Regularity suffices to compare silence and every randomized proposal. -/
theorem optimal_response (rule : RegularSelection Action) (prescribed : FinDist Action)
    (continuation : Action → FinDist Outcome) (utility : Outcome → ℝ)
    (optimal : ∀ action, (continuation action).expect utility ≤
      (prescribed.bind continuation).expect utility)
    (alternative : FinDist (Option Action)) :
    ((rule.responseLaw alternative).bind continuation).expect utility ≤
      ((rule.responseLaw (prescribed.map some)).bind continuation).expect utility := by
  let value := fun action => (continuation action).expect utility
  have best (action : Action) : value action ≤ prescribed.expect value := by
    simpa only [FinDist.expect_bind] using optimal action
  rw [FinDist.expect_bind, FinDist.expect_bind, submitted_value]
  rw [responseLaw, FinDist.expect_bind]
  change alternative.expect (fun response => (rule.includeLaw response).expect value) ≤ _
  apply FinDist.expect_le_of_forall
  intro response _
  cases response with
  | none =>
      have bound := rule.regular.expect_le
        (fun selected => selected.elim (prescribed.expect value) value)
        (fun selected => by cases selected with
          | none => exact le_rfl
          | some action => exact best action)
      simpa only [FinDist.expect_map, Option.elim_some, includeLaw] using bound
  | some action =>
      rw [includeLaw, FinDist.expect_map]
      apply FinDist.expect_mono
      intro selected _
      cases selected with
      | none => exact best action
      | some _ => exact le_rfl

theorem optimal_response_of_support (rule : RegularSelection Action)
    (prescribed recovered : FinDist Action) (continuation : Action → FinDist Outcome)
    (utility : Outcome → ℝ)
    (optimal : ∀ action, (continuation action).expect utility ≤
      (prescribed.bind continuation).expect utility)
    (supported : recovered.support ⊆ prescribed.support)
    (alternative : FinDist (Option Action)) :
    ((rule.responseLaw alternative).bind continuation).expect utility ≤
      ((rule.responseLaw (recovered.map some)).bind continuation).expect utility := by
  let value := fun action => (continuation action).expect utility
  have best (action : Action) : value action ≤ prescribed.expect value := by
    simpa only [FinDist.expect_bind] using optimal action
  have equal (action : Action) (member : action ∈ prescribed.support) :
      value action = prescribed.expect value :=
    prescribed.eq_of_expect_eq_of_le value _ (fun action _ => best action) rfl member
  have sameValue : recovered.expect value = prescribed.expect value := by
    calc
      recovered.expect value = recovered.expect (fun _ => prescribed.expect value) :=
        FinDist.expect_congr fun action member => equal action (supported member)
      _ = _ := FinDist.expect_const ..
  apply rule.optimal_response recovered continuation utility ?_ alternative
  intro action
  simpa only [FinDist.expect_bind, ← sameValue] using best action

/-- Independent fixed mixtures instantiate regular selection. -/
def ofMixture (retained : FinDist Action) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) : RegularSelection Action where
  retained := retained
  selection := FinDist.mix weight nonnegative atMostOne
    (FinDist.pure none) (retained.map some)
  regular := FinDist.regularAt_mix (retained.map some) none weight nonnegative atMostOne

theorem ofMixture_includeLaw (retained : FinDist Action) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (response : Option Action) :
    (ofMixture retained weight nonnegative atMostOne).includeLaw response =
      PendingChoice.includeLaw weight nonnegative atMostOne retained response := by
  cases response with
  | none => rfl
  | some action =>
      simp only [includeLaw, ofMixture, FinDist.map_mix, FinDist.map_pure, FinDist.map_comp,
        Option.getD_none, Function.comp_def, Option.getD_some, PendingChoice.includeLaw]
      change FinDist.mix weight nonnegative atMostOne (FinDist.pure action)
        (retained.map id) = _
      rw [FinDist.map_id]

def game (rule : RegularSelection Action) (continuation : Action → FinDist Outcome) :
    GameForm Unit where
  sig := { Strategy := fun _ => FinDist (Option Action), Outcome := Outcome }
  play profile := (rule.responseLaw (profile ())).bind continuation

theorem nash_preserved (rule : RegularSelection Action)
    (continuation : Action → FinDist Outcome) (utility : Outcome → Unit → ℝ)
    (prescribed : FinDist Action)
    (optimal : IsNash (sourceGame continuation) (euPreference utility) (fun _ => prescribed)) :
    IsNash (rule.game continuation) (euPreference utility) (fun _ => prescribed.map some) := by
  rw [isNash_iff] at optimal ⊢
  intro who alternative
  cases who
  apply rule.optimal_response prescribed continuation (utility · ()) ?_ alternative
  intro action
  have bound := optimal () (FinDist.pure action)
  simpa only [euPreference, expectedUtility, sourceGame, Profile.update_same,
    FinDist.pure_bind] using bound

end RegularSelection
end GameTheory.PendingChoice
