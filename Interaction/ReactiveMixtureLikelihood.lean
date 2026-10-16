/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMixtureAtoms
import GameTheoryExtensions.Math.Probability.NestedPosterior

/-! # Exact response likelihoods under immutable private-policy mixtures -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Memory : Type} (app : ReactiveApplication Principal)

private theorem response_density (prior : PMF Memory) (family : Memory → app.Policy)
    (past : List app.PlayerEntry) (entry : app.PlayerEntry) (memory : Memory) :
    (app.policyMixture prior family).policy past entry.beforeView entry.action *
        (app.policyMixture prior family).posterior (past ++ [entry]) memory =
      (app.policyMixture prior family).posterior past memory *
        family memory past entry.beforeView entry.action := by
  let before := (app.policyMixture prior family).posterior past
  let kernel := fun memory => family memory past entry.beforeView
  let joint := before.bind fun memory => (kernel memory).map fun action => (action, memory)
  have marginal : joint.map Prod.fst = (app.policyMixture prior family).policy past
      entry.beforeView := by
    rw [policyMixture_policy]
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact bind_congr_on_support before (fun _ _ => PMF.map_id _)
  have density := mul_fiberPosterior_map_snd_apply joint entry.action memory
  rw [marginal, bind_map_tag_apply] at density
  rw [Implementation.posterior_snoc]
  exact density

/-- A full observed response word weights its actual immutable-member
posterior by exactly its behavioral likelihood. The original prior at the
complete old recall is retained, including after impossible-word fallback. -/
theorem policyMixture_likelihood_density (prior : PMF Memory) (family : Memory → app.Policy)
    (earlier suffix : List app.PlayerEntry) (memory : Memory) :
    ((app.privateTranscriptFrom earlier suffix).map (fun record =>
      (app.policyMixture prior family).policy record.1.1 record.1.2 record.2)).prod *
        (app.policyMixture prior family).posterior (earlier ++ suffix) memory =
      (app.policyMixture prior family).posterior earlier memory *
        ((app.privateTranscriptFrom earlier suffix).map (fun record =>
          family memory record.1.1 record.1.2 record.2)).prod := by
  induction suffix using List.reverseRecOn with
  | nil => simp only [privateTranscriptFrom, List.map_nil, List.prod_nil, one_mul,
      List.append_nil, mul_one]
  | append_singleton suffix entry ih =>
      simp only [privateTranscriptFrom_append, privateTranscriptFrom,
        List.singleton_append, List.append_assoc]
      let first := ((app.privateTranscriptFrom earlier suffix).map (fun record =>
        (app.policyMixture prior family).policy record.1.1 record.1.2 record.2)).prod
      let second := ((app.privateTranscriptFrom earlier suffix).map (fun record =>
        family memory record.1.1 record.1.2 record.2)).prod
      let current := (app.policyMixture prior family).policy (earlier ++ suffix)
        entry.beforeView entry.action
      let member := family memory (earlier ++ suffix) entry.beforeView entry.action
      have step := response_density app prior family (earlier ++ suffix) entry memory
      change (current * first) * _ = _ * (member * second)
      calc
        _ = first * (current *
            (app.policyMixture prior family).posterior ((earlier ++ suffix) ++ [entry])
              memory) := by ac_rfl
        _ = first * ((app.policyMixture prior family).posterior (earlier ++ suffix) memory *
            member) := congrArg (first * ·) step
        _ = (first * (app.policyMixture prior family).posterior (earlier ++ suffix) memory) *
            member := by ac_rfl
        _ = ((app.policyMixture prior family).posterior earlier memory * second) * member :=
          congrArg (· * member) ih
        _ = _ := by ac_rfl

/-- The same exact observed-word density transports every subsequent
private-memory payoff. No new posterior, resampled entry law or likelihood
factorization hypothesis is introduced. -/
theorem policyMixture_likelihood_expect (prior : PMF Memory) (family : Memory → app.Policy)
    (earlier suffix : List app.PlayerEntry) (payoff : Memory → ℝ) :
    expect ((app.policyMixture prior family).posterior earlier) (fun memory =>
        (((app.privateTranscriptFrom earlier suffix).map (fun record =>
          family memory record.1.1 record.1.2 record.2)).prod).toReal * payoff memory) =
      (((app.privateTranscriptFrom earlier suffix).map (fun record =>
        (app.policyMixture prior family).policy record.1.1 record.1.2 record.2)).prod).toReal *
          expect ((app.policyMixture prior family).posterior (earlier ++ suffix)) payoff := by
  unfold expect
  rw [← tsum_mul_left]
  apply tsum_congr
  intro memory
  have density := congrArg ENNReal.toReal
    (policyMixture_likelihood_density app prior family earlier suffix memory)
  simp only [ENNReal.toReal_mul] at density
  calc
    _ = ((app.policyMixture prior family).posterior earlier memory).toReal *
        (((app.privateTranscriptFrom earlier suffix).map (fun record =>
          family memory record.1.1 record.1.2 record.2)).prod).toReal * payoff memory := by ring
    _ = _ := by rw [← density]; ring

/-- The actual recalled-response product equals the chronological indexed
product at the full original input of each recorded action. -/
theorem privateTranscriptFrom_product (policy : app.Policy)
    (earlier suffix : List app.PlayerEntry) :
    (((app.privateTranscriptFrom earlier suffix).map (fun record =>
      policy record.1.1 record.1.2 record.2)).prod).toReal =
      ∏ index : Fin suffix.length,
        (policy (earlier ++ suffix.take index.val) suffix[index.val].beforeView
          suffix[index.val].action).toReal := by
  induction suffix generalizing earlier with
  | nil => simp only [privateTranscriptFrom, List.map_nil, List.prod_nil, ENNReal.toReal_one,
      List.length_nil, Finset.univ_eq_empty, Finset.prod_empty]
  | cons entry suffix ih =>
      rw [privateTranscriptFrom, List.map_append, List.prod_append, ENNReal.toReal_mul, ih]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      simp only [List.length_cons]
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, List.append_nil, List.getElem_cons_zero]
      rw [mul_comm]
      apply congrArg (fun rest => (policy earlier entry.beforeView entry.action).toReal * rest)
      apply Finset.prod_congr rfl
      intro index _member
      simp only [Fin.val_succ, List.take_succ_cons, List.getElem_cons_succ,
        List.append_assoc, List.singleton_append]

/-- If an observed action does not update the law of the subsequent actual
likelihood, replacing ONLY its atom by a fixed marked mass commutes with
averaging the immutable original member. Old full recall remains explicit. -/
theorem policyMixture_marked_likelihood_expect (prior : PMF Memory) (family : Memory → app.Policy)
    (earlier before : List app.PlayerEntry) (entry : app.PlayerEntry)
    (after : List app.PlayerEntry) (raw : ℝ)
    (same :
      ((app.policyMixture prior family).posterior (earlier ++ before)).map
          (fun memory => (((app.privateTranscriptFrom ((earlier ++ before) ++ [entry]) after).map
            (fun record => family memory record.1.1 record.1.2 record.2)).prod).toReal) =
        ((app.policyMixture prior family).posterior ((earlier ++ before) ++ [entry])).map
          (fun memory => (((app.privateTranscriptFrom ((earlier ++ before) ++ [entry]) after).map
            (fun record => family memory record.1.1 record.1.2 record.2)).prod).toReal)) :
    expect ((app.policyMixture prior family).posterior earlier) (fun memory =>
        (((app.privateTranscriptFrom earlier before).map (fun record =>
          family memory record.1.1 record.1.2 record.2)).prod).toReal * raw *
            (((app.privateTranscriptFrom ((earlier ++ before) ++ [entry]) after).map (fun record =>
              family memory record.1.1 record.1.2 record.2)).prod).toReal) =
      (((app.privateTranscriptFrom earlier before).map (fun record =>
        (app.policyMixture prior family).policy record.1.1 record.1.2 record.2)).prod).toReal *
        raw *
          (((app.privateTranscriptFrom ((earlier ++ before) ++ [entry]) after).map (fun record =>
            (app.policyMixture prior family).policy record.1.1 record.1.2
              record.2)).prod).toReal := by
  let future := fun memory =>
    (((app.privateTranscriptFrom ((earlier ++ before) ++ [entry]) after).map (fun record =>
      family memory record.1.1 record.1.2 record.2)).prod).toReal
  have posteriorMean := congrArg (fun law : PMF ℝ => expect law id) same
  simp only [expect_map, Function.comp_def, id_eq] at posteriorMean
  have remaining := policyMixture_likelihood_expect app prior family
    ((earlier ++ before) ++ [entry]) after (fun _ => (1 : ℝ))
  simp only [mul_one, expect_constant] at remaining
  have beforeMean := policyMixture_likelihood_expect app prior family earlier before future
  have equality : (fun memory =>
      (((app.privateTranscriptFrom earlier before).map (fun record =>
        family memory record.1.1 record.1.2 record.2)).prod).toReal * raw * future memory) =
        fun memory => raw *
          ((((app.privateTranscriptFrom earlier before).map (fun record =>
            family memory record.1.1 record.1.2 record.2)).prod).toReal * future memory) := by
    funext memory
    ring
  change expect _ (fun memory => _ * raw * future memory) = _
  rw [equality, expect_const_mul, beforeMean]
  rw [posteriorMean, remaining]
  ring

end Interaction.ReactiveApplication
