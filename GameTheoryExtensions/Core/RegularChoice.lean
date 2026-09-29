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
  retained : PMF Action
  selection : PMF (Option Action)
  regular : (retained.map some).RegularAt selection none

namespace RegularSelection

/-- Decode a regular insertion. The fresh candidate has no old occurrence;
retained candidates may decode to the same source action. -/
def ofInsertion {Candidate : Type*} [DecidableEq Candidate]
    (before after : PMF Candidate) (fresh : Candidate)
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
      rw [PMF.map_comp]
      apply map_congr_on_support _
      intro candidate member
      have different : candidate ≠ fresh := fun same => absent (same ▸ member)
      simp only [different, ↓reduceIte, Function.comp_def]
    simpa only [old, ↓reduceIte] using mapped

def includeLaw (rule : RegularSelection Action) : Option Action → PMF Action
  | none => rule.retained
  | some action => rule.selection.map (fun selected => selected.getD action)

def responseLaw (rule : RegularSelection Action) (responses : PMF (Option Action)) :
    PMF Action := responses.bind rule.includeLaw

/-- Decoding a proposal substitutes the new source action at its fresh identity. -/
theorem ofInsertion_submit {Candidate : Type*} [DecidableEq Candidate]
    (before after : PMF Candidate) (fresh : Candidate)
    (absent : fresh ∉ before.support) (regular : before.RegularAt after fresh)
    (decode : Candidate → Action) (action : Action) :
    (ofInsertion before after fresh absent regular decode).includeLaw (some action) =
      after.map (fun candidate => if candidate = fresh then action else decode candidate) := by
  rw [includeLaw, ofInsertion, PMF.map_comp]
  apply map_congr_on_support _
  intro candidate _
  by_cases same : candidate = fresh <;> simp [same]

/-- Averaging the submitted action commutes with the independent selection. -/
theorem submitted_value (rule : RegularSelection Action) (law : PMF Action)
    (value : Action → ℝ) :
    expect (rule.responseLaw (law.map some)) value =
      expect rule.selection (fun selected => selected.elim (expect law value) value) := by
  simp only [responseLaw, FinDist.expect_bind, expect_map, includeLaw]
  rw [FinDist.expect_comm]
  apply expect_congr_on_support
  intro selected _
  cases selected <;> simp

/-- Regularity suffices to compare silence and every randomized proposal. -/
theorem optimal_response (rule : RegularSelection Action) (prescribed : PMF Action)
    (continuation : Action → PMF Outcome) (utility : Outcome → ℝ)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (alternative : PMF (Option Action)) :
    expect ((rule.responseLaw alternative).bind continuation) utility ≤
      expect ((rule.responseLaw (prescribed.map some)).bind continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [FinDist.expect_bind] using optimal action
  rw [FinDist.expect_bind, FinDist.expect_bind, submitted_value]
  rw [responseLaw, FinDist.expect_bind]
  change expect alternative (fun response => expect (rule.includeLaw response) value) ≤ _
  apply FinDist.expect_le_of_forall
  intro response _
  cases response with
  | none =>
      have bound := rule.regular.expect_le
        (fun selected => selected.elim (expect prescribed value) value)
        (fun selected => by cases selected with
          | none => exact le_rfl
          | some action => exact best action)
      simpa only [expect_map, Option.elim_some, includeLaw] using bound
  | some action =>
      rw [includeLaw, expect_map]
      apply FinDist.expect_mono
      intro selected _
      cases selected with
      | none => exact best action
      | some _ => exact le_rfl

theorem optimal_response_of_support (rule : RegularSelection Action)
    (prescribed recovered : PMF Action) (continuation : Action → PMF Outcome)
    (utility : Outcome → ℝ)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (supported : recovered.support ⊆ prescribed.support)
    (alternative : PMF (Option Action)) :
    expect ((rule.responseLaw alternative).bind continuation) utility ≤
      expect ((rule.responseLaw (recovered.map some)).bind continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [FinDist.expect_bind] using optimal action
  have equal (action : Action) (member : action ∈ prescribed.support) :
      value action = expect prescribed value :=
    prescribed.eq_of_expect_eq_of_le value _ (fun action _ => best action) rfl member
  have sameValue : expect recovered value = expect prescribed value := by
    calc
      expect recovered value = expect recovered (fun _ => expect prescribed value) :=
        expect_congr_on_support fun action member => equal action (supported member)
      _ = _ := expect_constant ..
  apply rule.optimal_response recovered continuation utility ?_ alternative
  intro action
  simpa only [FinDist.expect_bind, ← sameValue] using best action

/-- Independent fixed mixtures instantiate regular selection. -/
def ofMixture (retained : PMF Action) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) : RegularSelection Action where
  retained := retained
  selection := mix weight nonnegative atMostOne
    (PMF.pure none) (retained.map some)
  regular := PMF.regularAt_mix (retained.map some) none weight nonnegative atMostOne

theorem ofMixture_includeLaw (retained : PMF Action) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (response : Option Action) :
    (ofMixture retained weight nonnegative atMostOne).includeLaw response =
      PendingChoice.includeLaw weight nonnegative atMostOne retained response := by
  cases response with
  | none => rfl
  | some action =>
      simp only [includeLaw, ofMixture, mix_map, PMF.pure_map, PMF.map_comp,
        Option.getD_none, Function.comp_def, Option.getD_some, PendingChoice.includeLaw]
      change mix weight nonnegative atMostOne (PMF.pure action)
        (retained.map id) = _
      rw [PMF.map_id]

def game (rule : RegularSelection Action) (continuation : Action → PMF Outcome) :
    GameForm Unit where
  sig := { Strategy := fun _ => PMF (Option Action), Outcome := Outcome }
  play profile := (rule.responseLaw (profile ())).bind continuation

theorem nash_preserved (rule : RegularSelection Action)
    (continuation : Action → PMF Outcome) (utility : Outcome → Unit → ℝ)
    (prescribed : PMF Action)
    (optimal : IsNash (sourceGame continuation) (euPreference utility) (fun _ => prescribed)) :
    IsNash (rule.game continuation) (euPreference utility) (fun _ => prescribed.map some) := by
  rw [isNash_iff] at optimal ⊢
  intro who alternative
  cases who
  apply rule.optimal_response prescribed continuation (utility · ()) ?_ alternative
  intro action
  have bound := optimal () (PMF.pure action)
  simpa only [euPreference, expectedUtility, sourceGame, Profile.update_same,
    PMF.pure_bind] using bound

end RegularSelection
end GameTheory.PendingChoice
