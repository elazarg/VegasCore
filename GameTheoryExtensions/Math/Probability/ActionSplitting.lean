/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheory.Math.Probability.Convergence
import GameTheoryExtensions.Math.Probability.Support

/-! # Fully mixed splitting of finite private action aliases

A retraction identifies raw actions with their normal forms. Each normal action
is split over its finite fiber, mixing the canonical representative with a
uniform fiber draw. The projected law is exact at every perturbation, the raw
law is fully mixed when the normalized law is, and vanishing fiber noise
recovers the canonical lift. These local laws are used by the reactive finite
menu comparison; they make no claim about information-set beliefs on their own.
-/

noncomputable section

namespace PMF

open GameTheory.Math.Probability

open Filter

variable {Raw Normal : Type} [Fintype Raw]
  (project : Raw → Normal) (canonical : Normal → Raw)
  (retract : ∀ action, project (canonical action) = action)

def fiberUniform (action : Normal) : PMF Raw := by
  classical
  letI : Nonempty {raw : Raw // project raw = action} := ⟨⟨canonical action, retract action⟩⟩
  exact (PMF.uniformOfFintype {raw : Raw // project raw = action}).map Subtype.val

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
      map_congr_on_support _ fun raw member =>
        (fiberUniform_supported project canonical retract action raw).mp member
    _ = pure action := map_const _ _

def splitKernel (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (action : Normal) : PMF Raw :=
  mix weight nonnegative atMostOne (fiberUniform project canonical retract action)
    (pure (canonical action))

theorem splitKernel_project (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (action : Normal) :
    (splitKernel project canonical retract weight nonnegative atMostOne action).map project =
      pure action := by
  rw [splitKernel, mix_map, fiberUniform_project, PMF.pure_map, retract, mix_self]

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
  exact (PMF.mem_support_pure_iff _ _).mp projected

theorem splitKernel_fullFiber (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (positive : 0 < weight) (action : Normal) (raw : Raw)
    (member : project raw = action) :
    raw ∈ (splitKernel project canonical retract weight nonnegative atMostOne action).support :=
  mem_support_mix_left weight nonnegative atMostOne positive
    ((fiberUniform_supported project canonical retract action raw).mpr member)

theorem split_project (law : PMF Normal) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) :
    (law.bind (splitKernel project canonical retract weight nonnegative atMostOne)).map project =
      law := by
  rw [map_bind]
  simp only [splitKernel_project, bind_pure]

theorem split_fullSupport (law : PMF Normal) (mixed : FullSupport law)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (positive : 0 < weight) :
    FullSupport (law.bind (splitKernel project canonical retract weight nonnegative atMostOne)) :=
    by
  intro raw
  rw [support_bind]
  exact Set.mem_iUnion₂.mpr ⟨project raw, mixed _,
    splitKernel_fullFiber project canonical retract weight nonnegative atMostOne positive
      (project raw) raw rfl⟩

/-- The exact action factor used in factoring raw history reach probabilities. -/
theorem split_prob (law : PMF Normal) (weight : ℝ) (nonnegative : 0 ≤ weight)
    (atMostOne : weight ≤ 1) (raw : Raw) :
    ((law.bind (splitKernel project canonical retract weight nonnegative atMostOne)) raw).toReal =
      (law (project raw)).toReal *
        ((splitKernel project canonical retract weight nonnegative atMostOne (project raw))
            raw).toReal := by
  rw [bind_apply_of_unique_branch law _ raw (project raw) fun action _ member =>
    (splitKernel_supported project canonical retract weight nonnegative atMostOne
      action raw member).symm, ENNReal.toReal_mul]

/-- All action fibers use the same noise sequence. No subsequence is needed
for the strategy limit; beliefs are a separate obligation. -/
theorem split_converges (sequence : Nat → PMF Normal) (law : PMF Normal)
    (converges : PMFConvergesPointwise sequence law)
    (weight : Nat → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (atMostOne : ∀ n, weight n ≤ 1)
    (vanishes : Tendsto weight atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => (sequence n).bind
        (splitKernel project canonical retract (weight n) (nonnegative n) (atMostOne n)))
      (law.map canonical) := by
  rw [pmfConvergesPointwise_iff_toReal]
  intro raw
  have projected : ((law.map canonical) raw).toReal =
      (law (project raw)).toReal * ((pure (canonical (project raw))) raw).toReal := by
    rw [← bind_pure_comp, bind_apply_of_unique_branch law _ raw (project raw)
      fun action _ member => by
        have same := (PMF.mem_support_pure_iff _ _).mp member
        rw [same, retract], ENNReal.toReal_mul]
    rfl
  simp only [split_prob, splitKernel, mix_apply_toReal, projected]
  have zero := vanishes.mul_const
    (((fiberUniform project canonical retract (project raw)) raw).toReal)
  have one : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have canonicalLimit := (one.sub vanishes).mul_const
    (((pure (canonical (project raw))) raw).toReal)
  simpa only [zero_mul, sub_zero, one_mul, zero_add] using
    (converges.toReal (project raw)).mul (zero.add canonicalLimit)

end PMF
