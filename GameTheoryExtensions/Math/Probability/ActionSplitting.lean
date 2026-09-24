/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist
import GameTheory.Math.Probability.Convergence

/-! # Fully mixed splitting of finite private action aliases

A retraction identifies raw actions with their normal forms. Each normal action
is split over its finite fiber, mixing the canonical representative with a
uniform fiber draw. The projected law is exact at every perturbation, the raw
law is fully mixed when the normalized law is, and vanishing fiber noise
recovers the canonical lift. These local laws are used by the reactive finite
menu comparison; they make no claim about information-set beliefs on their own.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

open Filter

variable {Raw Normal : Type} [Fintype Raw]
  (project : Raw → Normal) (canonical : Normal → Raw)
  (retract : ∀ action, project (canonical action) = action)

def fiberUniform (action : Normal) : FinDist Raw := by
  classical
  letI : Nonempty {raw : Raw // project raw = action} := ⟨⟨canonical action, retract action⟩⟩
  exact (uniformOfFintype : FinDist {raw : Raw // project raw = action}).map Subtype.val

theorem fiberUniform_supported (action : Normal) (raw : Raw) :
    raw ∈ (fiberUniform project canonical retract action).support ↔ project raw = action := by
  classical
  let : Nonempty {raw : Raw // project raw = action} := ⟨⟨canonical action, retract action⟩⟩
  unfold fiberUniform
  rw [support_map]
  constructor
  · rintro ⟨candidate, _, rfl⟩
    exact candidate.2
  · intro member
    exact ⟨⟨raw, member⟩, mem_support_uniformOfFintype _, rfl⟩

theorem fiberUniform_project (action : Normal) :
    (fiberUniform project canonical retract action).map project = pure action := by
  calc
    _ = (fiberUniform project canonical retract action).map (fun _ => action) :=
      map_congr_of_eq_on_support fun raw member =>
        (fiberUniform_supported project canonical retract action raw).mp member
    _ = pure action := map_const _ _

def splitKernel (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (action : Normal) : FinDist Raw :=
  mix weight nonnegative atMostOne (fiberUniform project canonical retract action)
    (pure (canonical action))

theorem splitKernel_project (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (action : Normal) :
    (splitKernel project canonical retract weight nonnegative atMostOne action).map project =
      pure action := by
  rw [splitKernel, map_mix, fiberUniform_project, map_pure, retract, mix_self]

theorem splitKernel_supported (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (action : Normal) (raw : Raw)
    (member : raw ∈ (splitKernel project canonical retract weight
      nonnegative atMostOne action).support) : project raw = action := by
  have projected : project raw ∈
      ((splitKernel project canonical retract weight nonnegative atMostOne action).map
        project).support := by
    rw [support_map]
    exact ⟨raw, member, rfl⟩
  rw [splitKernel_project] at projected
  exact mem_support_pure.mp projected

theorem splitKernel_fullFiber (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (positive : 0 < weight) (action : Normal) (raw : Raw)
    (member : project raw = action) :
    raw ∈ (splitKernel project canonical retract weight nonnegative atMostOne action).support :=
  mem_support_mix_left weight nonnegative atMostOne positive
    ((fiberUniform_supported project canonical retract action raw).mpr member)

theorem split_project (law : FinDist Normal) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) :
    (law.bind (splitKernel project canonical retract weight nonnegative atMostOne)).map project =
      law := by
  rw [map_bind]
  simp only [splitKernel_project, bind_pure]

theorem split_fullSupport (law : FinDist Normal) (mixed : law.FullSupport)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (positive : 0 < weight) :
    (law.bind (splitKernel project canonical retract weight nonnegative atMostOne)).FullSupport :=
    by
  intro raw
  rw [support_bind]
  exact Set.mem_iUnion₂.mpr ⟨project raw, mixed _,
    splitKernel_fullFiber project canonical retract weight nonnegative atMostOne positive
      (project raw) raw rfl⟩

/-- The exact action factor used in factoring raw history reach probabilities. -/
theorem split_prob (law : FinDist Normal) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (raw : Raw) :
    (law.bind (splitKernel project canonical retract weight nonnegative atMostOne)).prob raw =
      law.prob (project raw) *
        (splitKernel project canonical retract weight nonnegative atMostOne (project raw)).prob
          raw := by
  apply prob_bind_of_unique_branch
  intro action _ member
  exact (splitKernel_supported project canonical retract weight nonnegative atMostOne
    action raw member).symm

/-- All action fibers use the same noise sequence. No subsequence is needed
for the strategy limit; beliefs are a separate obligation. -/
theorem split_converges (sequence : Nat → FinDist Normal) (law : FinDist Normal)
    (converges : FinDistConvergesPointwise sequence law)
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) :
    FinDistConvergesPointwise
      (fun n => (sequence n).bind
        (splitKernel project canonical retract (weight n) (nonnegative n) (atMostOne n)))
      (law.map canonical) := by
  intro raw
  have projected : (law.map canonical).prob raw =
      law.prob (project raw) * (pure (canonical (project raw))).prob raw := by
    rw [map_eq_bind]
    apply prob_bind_of_unique_branch
    intro action _ member
    have same := mem_support_pure.mp member
    rw [same, retract]
  simp only [split_prob, splitKernel, prob_mix, projected]
  have zero := vanishes.mul_const
    ((fiberUniform project canonical retract (project raw)).prob raw)
  have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have canonicalLimit := (one.sub vanishes).mul_const
    ((pure (canonical (project raw))).prob raw)
  simpa only [zero_mul, sub_zero, one_mul, zero_add] using
    (converges (project raw)).mul (zero.add canonicalLimit)

end GameTheory.Math.Probability.FinDist
