/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.PendingChoice
import GameTheoryExtensions.Math.Probability.Regularity
import GameTheoryExtensions.Math.Probability.Support

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

/-- Submitting a sampled action is selecting first and then resolving the fresh
candidate by the sample. -/
theorem responseLaw_submitted (rule : RegularSelection Action) (law : PMF Action) :
    rule.responseLaw (law.map some) =
      rule.selection.bind fun selected => selected.elim law PMF.pure := by
  rw [responseLaw, PMF.bind_map]
  simp only [Function.comp_def, includeLaw, ← PMF.bind_pure_comp]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro selected _
  cases selected with
  | none => exact PMF.bind_pure law
  | some action =>
      simp only [Option.getD_some, Option.elim_some]
      exact PMF.bind_const law _

/-- Averaging the submitted action commutes with the independent selection. -/
theorem submitted_value (rule : RegularSelection Action) (law : PMF Action)
    (value : Action → ℝ)
    (integrable : PayoffIntegrable (rule.responseLaw (law.map some)) value) :
    expect (rule.responseLaw (law.map some)) value =
      expect rule.selection (fun selected => selected.elim (expect law value) value) := by
  rw [responseLaw_submitted] at integrable ⊢
  rw [expect_bind_tower _ _ _ integrable]
  apply expect_congr_on_support
  intro selected _
  cases selected <;> simp [expect_pure]

/-- Regularity suffices to compare silence and every randomized proposal.
The compared laws must have finite expected utility. -/
theorem optimal_response (rule : RegularSelection Action) (prescribed : PMF Action)
    (continuation : Action → PMF Outcome) (utility : Outcome → ℝ)
    (prescribedIntegrable : PayoffIntegrable (prescribed.bind continuation) utility)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (submittedIntegrable : PayoffIntegrable
      ((rule.responseLaw (prescribed.map some)).bind continuation) utility)
    (alternative : PMF (Option Action))
    (alternativeIntegrable : PayoffIntegrable
      ((rule.responseLaw alternative).bind continuation) utility) :
    expect ((rule.responseLaw alternative).bind continuation) utility ≤
      expect ((rule.responseLaw (prescribed.map some)).bind continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [expect_bind_tower _ _ _ prescribedIntegrable] using optimal action
  have submittedValue := payoffIntegrable_bind_conditionalExpectation _ _ _ submittedIntegrable
  have selectionValue : PayoffIntegrable rule.selection
      (fun selected => selected.elim (expect prescribed value) value) := by
    have conditional := submittedValue
    rw [responseLaw_submitted] at conditional
    have mapped := payoffIntegrable_bind_conditionalExpectation _ _ _ conditional
    refine payoffIntegrable_congr_on_support (fun selected _ => ?_) mapped
    cases selected <;> simp [expect_pure, value]
  rw [expect_bind_tower _ _ _ submittedIntegrable, submitted_value _ _ _ submittedValue,
    expect_bind_tower _ _ _ alternativeIntegrable]
  have alternativeValue := payoffIntegrable_bind_conditionalExpectation _ _ _ alternativeIntegrable
  rw [responseLaw] at alternativeValue ⊢
  rw [expect_bind_tower _ _ _ alternativeValue]
  apply expect_le_const _ _
    (payoffIntegrable_bind_conditionalExpectation _ _ _ alternativeValue)
  intro response supported
  have branch := payoffIntegrable_bind_conditional_on_support _ _ _ alternativeValue response
    supported
  cases response with
  | none =>
      have retained : PayoffIntegrable (rule.retained.map some)
          (fun selected => selected.elim (expect prescribed value) value) := by
        rw [payoffIntegrable_map_iff]
        exact branch
      have bound := rule.regular.expect_le
        (fun selected => selected.elim (expect prescribed value) value)
        (fun selected => by cases selected with
          | none => exact le_rfl
          | some action => exact best action) retained selectionValue
      simpa only [expect_map, Function.comp_def, Option.elim_some, includeLaw] using bound
  | some action =>
      rw [includeLaw, expect_map]
      rw [includeLaw, payoffIntegrable_map_iff] at branch
      apply expect_mono _ branch selectionValue
      intro selected _
      cases selected with
      | none => exact best action
      | some _ => exact le_rfl

theorem optimal_response_of_support (rule : RegularSelection Action)
    (prescribed recovered : PMF Action) (continuation : Action → PMF Outcome)
    (utility : Outcome → ℝ)
    (prescribedIntegrable : PayoffIntegrable (prescribed.bind continuation) utility)
    (recoveredIntegrable : PayoffIntegrable (recovered.bind continuation) utility)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (prescribed.bind continuation) utility)
    (supported : recovered.support ⊆ prescribed.support)
    (submittedIntegrable : PayoffIntegrable
      ((rule.responseLaw (recovered.map some)).bind continuation) utility)
    (alternative : PMF (Option Action))
    (alternativeIntegrable : PayoffIntegrable
      ((rule.responseLaw alternative).bind continuation) utility) :
    expect ((rule.responseLaw alternative).bind continuation) utility ≤
      expect ((rule.responseLaw (recovered.map some)).bind continuation) utility := by
  let value := fun action => expect (continuation action) utility
  have prescribedValue := expect_bind_tower _ _ _ prescribedIntegrable
  have best (action : Action) : value action ≤ expect prescribed value := by
    simpa only [prescribedValue] using optimal action
  have equal := expect_eq_const_of_le_on_support prescribed value _
    (payoffIntegrable_bind_conditionalExpectation _ _ _ prescribedIntegrable)
    (fun action _ => best action) rfl
  have sameValue : expect recovered value = expect prescribed value := by
    calc
      expect recovered value = expect recovered (fun _ => expect prescribed value) :=
        expect_congr_on_support fun action member => equal action (supported member)
      _ = _ := expect_constant ..
  apply rule.optimal_response recovered continuation utility recoveredIntegrable ?_
    submittedIntegrable alternative alternativeIntegrable
  intro action
  rw [expect_bind_tower _ _ _ recoveredIntegrable]
  simpa only [← sameValue] using best action

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

/-- Nash equilibrium of the source choice carries over whenever every
response deviation has a finite expected utility. Every finitely supported
instance satisfies that premise. -/
theorem nash_preserved (rule : RegularSelection Action)
    (continuation : Action → PMF Outcome) (utility : Outcome → Unit → ℝ)
    (prescribed : PMF Action)
    (optimal : IsNash (sourceGame continuation) (euPreference utility) (fun _ => prescribed))
    (integrable : ∀ alternative : PMF (Option Action), PayoffIntegrable
      ((rule.responseLaw alternative).bind continuation) (utility · ()))
    (sourceIntegrable : ∀ action, PayoffIntegrable (continuation action) (utility · ()))
    (prescribedIntegrable : PayoffIntegrable (prescribed.bind continuation) (utility · ())) :
    IsNash (rule.game continuation) (euPreference utility) (fun _ => prescribed.map some) := by
  rw [isNash_iff] at optimal ⊢
  intro who alternative
  cases who
  refine (euPreference_iff utility () _ _ (integrable _) (integrable _)).mpr ?_
  apply rule.optimal_response prescribed continuation (utility · ()) prescribedIntegrable ?_
    (integrable _) alternative (integrable _)
  intro action
  have bound := optimal () (PMF.pure action)
  simp only [sourceGame, Profile.update_same, PMF.pure_bind] at bound
  exact (euPreference_iff utility () _ _ prescribedIntegrable (sourceIntegrable action)).mp bound

end RegularSelection
end GameTheory.PendingChoice
