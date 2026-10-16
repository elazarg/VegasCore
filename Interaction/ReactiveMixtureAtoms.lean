/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyMixture

/-! # Private-memory conditioning through actual recorded response atoms -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Index : Type} (app : ReactiveApplication Principal)

private theorem update_congr_atoms (initial : PMF Index)
    (first second : Index → PMF app.Action) (observed : app.Action)
    (same : ∀ index, first index observed = second index observed) :
    (fiberPosterior (initial.bind fun index =>
        (first index).map (fun action => (action, index))) Prod.fst observed).map Prod.snd =
      (fiberPosterior (initial.bind fun index =>
        (second index).map (fun action => (action, index))) Prod.fst observed).map Prod.snd := by
  let joint := fun family : Index → PMF app.Action =>
    initial.bind fun index => (family index).map (fun action => (action, index))
  have row (family : Index → PMF app.Action) (action : app.Action) (index : Index) :
      joint family (action, index) = initial index * family index action := by
    have swapped : joint family = (bindPairLaw initial family).map Prod.swap := by
      simp only [joint, bindPairLaw, PMF.map_bind, PMF.map_comp]
      rfl
    rw [swapped, show (action, index) = Prod.swap (index, action) from rfl,
      pmf_map_apply_of_injective _ Prod.swap_injective, bindPairLaw_apply]
  have marginal (family : Index → PMF app.Action) :
      (joint family).map Prod.fst = initial.bind family := by
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact bind_congr_on_support _ fun _ _ => PMF.map_id _
  have sameMass : ((joint first).map Prod.fst) observed =
      ((joint second).map Prod.fst) observed := by
    rw [marginal, marginal, PMF.bind_apply, PMF.bind_apply]
    exact tsum_congr fun index => congrArg (initial index * ·) (same index)
  change (fiberPosterior (joint first) Prod.fst observed).map Prod.snd =
    (fiberPosterior (joint second) Prod.fst observed).map Prod.snd
  by_cases present : observed ∈ ((joint first).map Prod.fst).support
  · have nextPresent : observed ∈ ((joint second).map Prod.fst).support := by
      simpa only [PMF.mem_support_iff, ← sameMass] using present
    ext index
    rw [fiberPosterior_map_snd_apply _ _ present,
      fiberPosterior_map_snd_apply _ _ nextPresent, row, row, same index, sameMass]
  · have nextAbsent : observed ∉ ((joint second).map Prod.fst).support := by
      simpa only [PMF.mem_support_iff, ← sameMass] using present
    rw [fiberPosterior_of_not_mem_support _ _ present,
      fiberPosterior_of_not_mem_support _ _ nextAbsent]
    have retained (family : Index → PMF app.Action) :
        (joint family).map Prod.snd = initial := by
      simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
      calc
        _ = initial.bind (fun index => PMF.pure index) := by
          apply bind_congr_on_support
          intro index _supported
          exact PMF.map_const _ _
        _ = _ := PMF.bind_pure initial
    rw [retained, retained]

/-- Equal likelihoods of each actual recalled response give the same private
posterior. Other response atoms may differ, and zero-likelihood fallback is
retained exactly. No source interpretation of the recalled actions is used. -/
theorem policyMixture_posterior_congr_atoms (initial : PMF Index)
    (first second : Index → app.Policy) (past : List app.PlayerEntry)
    (same : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past → ∀ index,
        first index before entry.beforeView entry.action =
          second index before entry.beforeView entry.action) :
    (app.policyMixture initial first).posterior past =
      (app.policyMixture initial second).posterior past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier := ih fun before recorded inside =>
        same before recorded (inside.trans (List.prefix_append _ _))
      rw [Implementation.posterior_snoc, Implementation.posterior_snoc, earlier]
      exact update_congr_atoms app _ _ _ entry.action
        (same past entry (List.prefix_refl _))

/-- A coordinate unobserved by the actual response atoms retains its original
law independently of the updated remainder. The policies can still query that
coordinate while waiting; equality of entire response laws is unnecessary. -/
theorem policyMixture_posterior_independent_left_atoms {Local Rest : Type}
    (first : PMF Local) (restLaw : PMF Rest)
    (members : Local × Rest → app.Policy) (remainder : Rest → app.Policy)
    (past : List app.PlayerEntry)
    (unread : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past → ∀ value rest,
        members (value, rest) before entry.beforeView entry.action =
          remainder rest before entry.beforeView entry.action) :
    (app.policyMixture (first.bind fun value => restLaw.map (Prod.mk value))
      members).posterior past =
      first.bind (fun value => ((app.policyMixture restLaw remainder).posterior past).map
        (Prod.mk value)) := by
  trans (app.policyMixture (first.bind fun value => restLaw.map (Prod.mk value))
    (fun pair => remainder pair.2)).posterior past
  · exact app.policyMixture_posterior_congr_atoms _ _ _ past
      (fun before entry inside pair => unread before entry inside pair.1 pair.2)
  · exact app.policyMixture_posterior_independent_left first restLaw _ remainder past
      (fun _before _entry _inside _value _rest => rfl)

end Interaction.ReactiveApplication
