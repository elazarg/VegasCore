/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMixtureRecall
import GameTheoryExtensions.Math.Probability.NestedPosterior

/-! # Hierarchical immutable policy mixtures at the same complete own recall -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Plan Word : Type} (app : ReactiveApplication Principal)

/-- A supported complete recall disintegrates the original plan-and-word
posterior into its actual plan posterior and the same-recall word posterior
for that plan. The outer behavioral mixture supports that same recall. -/
theorem policyMixture_hierarchical (weights : PMF Plan) (prior : PMF Word)
    (family : Plan → Word → app.Policy) (past : List app.PlayerEntry)
    (consistent : (app.policyMixture
      (weights.bind fun plan => prior.map (Prod.mk plan))
      (fun pair => family pair.1 pair.2)).policy.Consistent past) :
    (app.policyMixture (weights.bind fun plan => prior.map (Prod.mk plan))
        (fun pair => family pair.1 pair.2)).posterior past =
      ((app.policyMixture weights
        (fun plan => (app.policyMixture prior (family plan)).policy)).posterior past).bind
          (fun plan => ((app.policyMixture prior (family plan)).posterior past).map
            (Prod.mk plan)) ∧
      (app.policyMixture weights
        (fun plan => (app.policyMixture prior (family plan)).policy)).policy.Consistent past := by
  let flat := app.policyMixture (weights.bind fun plan => prior.map (Prod.mk plan))
    (fun pair => family pair.1 pair.2)
  let inner := fun plan => app.policyMixture prior (family plan)
  let outer := app.policyMixture weights (fun plan => (inner plan).policy)
  change flat.posterior past = (outer.posterior past).bind
    (fun plan => ((inner plan).posterior past).map (Prod.mk plan)) ∧
      outer.policy.Consistent past
  induction consistent with
  | nil => exact ⟨rfl, .nil⟩
  | @snoc past entry _consistent sampled ih =>
    have policyEq : flat.policy past entry.beforeView = outer.policy past entry.beforeView := by
      rw [policyMixture_policy, policyMixture_policy, ih.1]
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      apply bind_congr_on_support
      intro plan _member
      exact (app.policyMixture_policy prior (family plan) past entry.beforeView).symm
    have outerSample : entry.action ∈ (outer.policy past entry.beforeView).support := by
      rw [← policyEq]
      exact sampled
    refine ⟨?_, .snoc entry ih.2 outerSample⟩
    let kernel := fun plan => ((inner plan).posterior past).bind fun word =>
      (family plan word past entry.beforeView).map fun action => (action, word)
    have kernelMarginal (plan : Plan) : (kernel plan).map Prod.fst =
        (inner plan).policy past entry.beforeView := by
      rw [policyMixture_policy]
      simp only [kernel, PMF.map_bind, PMF.map_comp]
      apply bind_congr_on_support
      intro word _member
      exact PMF.map_id _
    have present : entry.action ∈ ((outer.posterior past).bind fun plan =>
        (kernel plan).map Prod.fst).support := by
      simp_rw [kernelMarginal]
      rw [← policyMixture_policy]
      exact outerSample
    have factor := fiberPosterior_hierarchical_pair (outer.posterior past) kernel
      entry.action present
    have flatJoint : (flat.posterior past).bind
        (fun pair => (family pair.1 pair.2 past entry.beforeView).map
          fun action => (action, pair)) =
        (bindPairLaw (outer.posterior past) kernel).map
          (fun pair => (pair.2.1, (pair.1, pair.2.2))) := by
      rw [ih.1]
      simp only [kernel, bindPairLaw, PMF.bind_bind, PMF.bind_map, PMF.map_bind,
        PMF.map_comp, Function.comp_def]
    have outerJoint : (outer.posterior past).bind
        (fun plan => ((inner plan).policy past entry.beforeView).map
          fun action => (action, plan)) =
        (outer.posterior past).bind (fun plan => ((kernel plan).map Prod.fst).map
          fun action => (action, plan)) := by
      simp_rw [kernelMarginal]
    simp_rw [Implementation.posterior_snoc]
    change (fiberPosterior ((flat.posterior past).bind
      (fun pair => (family pair.1 pair.2 past entry.beforeView).map
        fun action => (action, pair))) Prod.fst entry.action).map Prod.snd = _
    rw [flatJoint]
    change _ = ((fiberPosterior ((outer.posterior past).bind
      (fun plan => ((inner plan).policy past entry.beforeView).map
        fun action => (action, plan))) Prod.fst entry.action).map Prod.snd).bind
          (fun plan => ((fiberPosterior (kernel plan) Prod.fst entry.action).map Prod.snd).map
            (Prod.mk plan))
    rw [outerJoint]
    exact factor

end Interaction.ReactiveApplication
