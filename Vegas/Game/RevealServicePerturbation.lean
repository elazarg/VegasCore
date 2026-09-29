/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePolicy
import GameTheoryExtensions.Math.Probability.ActionSplitting
import GameTheoryExtensions.Math.Probability.Convergence

/-! # Common perturbations of the actual response compiler

Positive alias weights give every physical representative positive mass.
Vanishing alias weights recover the canonical compiler while preserving
convergence of the source Boolean choice laws. These local facts are used at
the source checkpoints established by the operational history proofs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

theorem ordinaryPolicy_at_opening (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (opening : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some opening)
    (covered : opening ∈ (bounds.menu (runtime setup) leaks).actions who past view) :
    ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne who past view =
      (splitChoiceLaw setup leaks bounds who past view opening selected covered
        (sourceChoiceLaw setup leaks profile who view) weight nonnegative atMostOne).map
          Subtype.val := by
  unfold ordinaryPolicy
  split
  · rename_i absent
    rw [selected] at absent
    cases absent
  · rename_i chosen found
    cases Option.some.inj (found.symm.trans selected)
    rw [dite_eq_left covered]

private theorem ordinaryPolicy_unavailable (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (unavailable : ∀ opening, opening? setup leaks who past view = some opening →
      opening ∉ (bounds.menu (runtime setup) leaks).actions who past view) :
    ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne who past view =
      PMF.pure ⟨none⟩ := by
  unfold ordinaryPolicy
  split
  · rfl
  · rename_i chosen found
    exact dite_eq_right (unavailable chosen found)

theorem ordinaryPolicy_support (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (positive : 0 < weight)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (opening : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some opening)
    (covered : opening ∈ (bounds.menu (runtime setup) leaks).actions who past view)
    (mixed : FullSupport (sourceChoiceLaw setup leaks profile who view))
    (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds who past view) :
    response ∈ (ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne
      who past view).support := by
  rw [ordinaryPolicy_at_opening setup leaks bounds profile weight nonnegative atMostOne
    who past view opening selected covered, PMF.support_map]
  exact ⟨⟨response, member⟩, splitChoiceLaw_fullSupport setup leaks bounds who past view
    opening selected covered _ mixed weight nonnegative atMostOne positive ⟨response, member⟩,
    rfl⟩

theorem splitChoiceLaw_zero
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (opening : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some opening)
    (covered : opening ∈ (bounds.menu (runtime setup) leaks).actions who past view)
    (law : PMF Bool) :
    splitChoiceLaw setup leaks bounds who past view opening selected covered law
        0 le_rfl (by norm_num) =
      law.map
        (canonicalOrdinaryChoice setup leaks bounds who past view opening selected covered) := by
  rw [splitChoiceLaw, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro disclose _supported
  exact mix_zero _ _

theorem ordinaryPolicy_converges
    (sequence : Nat → BehavioralProfile setup.program) (profile : BehavioralProfile setup.program)
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0))
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (choices : PMFConvergesPointwise
      (fun n => sourceChoiceLaw setup leaks (sequence n) who view)
      (sourceChoiceLaw setup leaks profile who view)) :
    PMFConvergesPointwise
      (fun n => ordinaryPolicy setup leaks bounds (sequence n) (weight n)
        (nonnegative n) (atMostOne n) who past view)
      (ordinaryPolicy setup leaks bounds profile 0 le_rfl (by norm_num) who past view) := by
  classical
  cases selected : opening? setup leaks who past view with
  | none =>
      have unavailable (opening : (application setup leaks).Action)
          (found : opening? setup leaks who past view = some opening) :
          opening ∉ (bounds.menu (runtime setup) leaks).actions who past view := by
        rw [selected] at found
        cases found
      simp only [ordinaryPolicy_unavailable setup leaks bounds _ _ _ _ who past view unavailable]
      exact pmfConvergesPointwise_const _
  | some opening =>
      by_cases covered : opening ∈ (bounds.menu (runtime setup) leaks).actions who past view
      · have convergence := PMF.split_converges
          (fun response : {response // response ∈ ordinaryActions setup leaks bounds who past view}
            => sourceChoice setup leaks response.1)
          (canonicalOrdinaryChoice setup leaks bounds who past view opening selected covered)
          (sourceChoice_canonical setup leaks bounds who past view opening selected covered)
          _ _ choices weight nonnegative atMostOne vanishes
        have mapped := convergence.map Subtype.val
        simp only [ordinaryPolicy_at_opening setup leaks bounds _ _ _ _ who past view
          opening selected covered, splitChoiceLaw_zero]
        exact mapped
      · have unavailable (chosen : (application setup leaks).Action)
            (found : opening? setup leaks who past view = some chosen) :
            chosen ∉ (bounds.menu (runtime setup) leaks).actions who past view := by
          cases Option.some.inj (found.symm.trans selected)
          exact covered
        simp only [ordinaryPolicy_unavailable setup leaks bounds _ _ _ _ who past view unavailable]
        exact pmfConvergesPointwise_const _

/-- The finite behavioral policy retains precisely the physical response law;
subtype witnesses introduce no further randomization. -/
theorem compiledProfile_map_val (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    ((compiledProfile setup leaks bounds watcher profile weight nonnegative atMostOne who)
      (some (past, view))).map Subtype.val =
      (policy setup leaks bounds watcher profile weight nonnegative atMostOne who past view).map
        some := by
  simp only [compiledProfile, ReactiveApplication.ResponseMenu.restrictPolicy,
    dite_eq_left (policy_covered setup leaks bounds watcher profile weight nonnegative
      atMostOne who past view), map_bindOnSupport, PMF.pure_map]
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bindOnSupport_eq_bind_of_eq_on_support _
  intro response supported
  rfl

theorem compiledProfile_converges_at
    (watcher : Player) (sequence : Nat → BehavioralProfile setup.program)
    (profile : BehavioralProfile setup.program)
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0))
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (choices : who ≠ watcher → PMFConvergesPointwise
      (fun n => sourceChoiceLaw setup leaks (sequence n) who view)
      (sourceChoiceLaw setup leaks profile who view)) :
    PMFConvergesPointwise
      (fun n => compiledProfile setup leaks bounds watcher (sequence n) (weight n)
        (nonnegative n) (atMostOne n) who (some (past, view)))
      (compiledProfile setup leaks bounds watcher profile 0 le_rfl (by norm_num)
        who (some (past, view))) := by
  classical
  have physical : PMFConvergesPointwise
      (fun n => policy setup leaks bounds watcher (sequence n) (weight n)
        (nonnegative n) (atMostOne n) who past view)
      (policy setup leaks bounds watcher profile 0 le_rfl (by norm_num) who past view) := by
    by_cases watches : who = watcher
    · simpa only [policy, watches, ↓reduceIte] using
        pmfConvergesPointwise_const
          ((application setup leaks).reportFirstUnpublished past view)
    · simpa only [policy, ite_eq_right watches] using
        ordinaryPolicy_converges setup leaks bounds sequence profile weight nonnegative
          atMostOne vanishes who past view (choices watches)
  intro choice
  have probabilities (current : BehavioralProfile setup.program) (w : ℝ)
      (nonneg : 0 ≤ w) (small : w ≤ 1) :
      ((compiledProfile setup leaks bounds watcher current w nonneg small who
        (some (past, view))) choice).toReal =
        (((policy setup leaks bounds watcher current w nonneg small who past view).map
          some) choice.1).toReal := by
    rw [← compiledProfile_map_val setup leaks bounds watcher current w nonneg small who past view,
      FinDist.prob_map_of_injective Subtype.val Subtype.val_injective]
  simp_rw [probabilities]
  obtain ⟨response, _member, value⟩ := choice.2
  rw [value]
  simp only [FinDist.prob_map_of_injective _ (Option.some_injective _)]
  exact physical response

end Vegas
