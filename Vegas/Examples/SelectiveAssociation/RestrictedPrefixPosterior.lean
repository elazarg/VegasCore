/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.RestrictedPrefixComparison
import Vegas.Examples.SelectiveAssociation.RestrictedPrefixInjection

/-! # Joint native information and binding probabilities

Each information event fixes Alice's accepted handle. Flipping that one handle
is an involution on the response tuples, preserves the guesser's whole input,
and weakly increases the probability of every true-binding tuple. The resulting
event inequalities retain failed bindings without assigning them either bit.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.Restricted.Prefix

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability PrefixSymmetry

theorem carol_joint_le (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (uncertified : publicGuess view = false) :
    ((carolLaw (mixed weight positive.le atMostOne)).toOuterMeasure {responses |
      ((carolInput responses).recall carol, (carolInput responses).observe app carol) =
        (past, view) ∧
      aliceBindingRef.get? (carolInput responses).application.config.store =
        some (.success true)}).toReal ≤
    ((carolLaw (mixed weight positive.le atMostOne)).toOuterMeasure {responses |
      ((carolInput responses).recall carol, (carolInput responses).observe app carol) =
        (past, view) ∧
      aliceBindingRef.get? (carolInput responses).application.config.store =
        some (.success false)}).toReal := by
  let players := (menu.perturbedAssessment (PMF.pure nativeInitial) nativeHorizon scheduler
    profile weight positive atMostOne).strategy
  have decoded : menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler players =
      mixed weight positive.le atMostOne := decode_perturbed weight positive atMostOne
  let selected : Handle nativeGraph :=
    (view.application.publicView.accepted aliceBindingRef.field).getD (alice, .prepared 0)
  let law := carolLaw (mixed weight positive.le atMostOne)
  let event (bit : Bool) : Set CarolResponses := {responses |
    ((carolInput responses).recall carol, (carolInput responses).observe app carol) =
      (past, view) ∧
    aliceBindingRef.get? (carolInput responses).application.config.store = some (.success bit)}
  have moves (responses : CarolResponses) (member : responses ∈ event true)
      (supported : responses ∈ law.support) :
      flipCarol selected responses ∈ event false ∧
        (law responses).toReal ≤ (law (flipCarol selected responses)).toReal := by
    have support : responses ∈ (carolLaw (menu.decodeProfile (PMF.pure nativeInitial)
        nativeHorizon scheduler players)).support := by
      rw [decoded]
      exact supported
    let control : app.Control := ⟨80, some carol, carolInput responses⟩
    obtain ⟨trace⟩ : Nonempty (arena.Trace (some control)) := carol_legal players responses support
    have observed := congrArg Prod.snd member.1
    dsimp only at observed
    obtain ⟨owner, associated, fixed⟩ :=
      true_view_handle control trace carol view observed member.2
    have hidden : publicGuess ((carolInput responses).observe app carol) = false := by
      rw [observed]
      exact uncertified
    obtain ⟨related, sameInput⟩ :=
      carol_flip_facts players responses support selected owner associated fixed hidden
    refine ⟨⟨sameInput.trans member.1, related_true_false selected _ _ related member.2⟩, ?_⟩
    exact carol_flip_probability weight positive.le atMostOne selected owner responses
      (carol_true_response_different players responses support member.2)
  exact ENNReal.toReal_mono (outerMeasure_ne_top law _)
    (toOuterMeasure_le_of_injection law (event true) (event false) (flipCarol selected)
      (fun _ _ _ _ same => (flipCarol_involutive selected).injective same)
      (fun responses member supported => (moves responses member supported).1)
      (fun responses member supported => (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _)).mp (moves responses member supported).2))

theorem bob_joint_le (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (uncertified : publicGuess view = false) :
    ((bobLaw (mixed weight positive.le atMostOne)).toOuterMeasure {responses |
      ((bobInput responses).recall bob, (bobInput responses).observe app bob) = (past, view) ∧
      aliceBindingRef.get? (bobInput responses).application.config.store = some
          (.success true)}).toReal ≤
    ((bobLaw (mixed weight positive.le atMostOne)).toOuterMeasure {responses |
      ((bobInput responses).recall bob, (bobInput responses).observe app bob) = (past, view) ∧
      aliceBindingRef.get? (bobInput responses).application.config.store =
        some (.success false)}).toReal := by
  let players := (menu.perturbedAssessment (PMF.pure nativeInitial) nativeHorizon scheduler
    profile weight positive atMostOne).strategy
  have decoded : menu.decodeProfile (PMF.pure nativeInitial) nativeHorizon scheduler players =
      mixed weight positive.le atMostOne := decode_perturbed weight positive atMostOne
  let selected : Handle nativeGraph :=
    (view.application.publicView.accepted aliceBindingRef.field).getD (alice, .prepared 0)
  let law := bobLaw (mixed weight positive.le atMostOne)
  let event (bit : Bool) : Set BobResponses := {responses |
    ((bobInput responses).recall bob, (bobInput responses).observe app bob) = (past, view) ∧
    aliceBindingRef.get? (bobInput responses).application.config.store = some (.success bit)}
  have moves (responses : BobResponses) (member : responses ∈ event true)
      (supported : responses ∈ law.support) :
      flipBob selected responses ∈ event false ∧
        (law responses).toReal ≤ (law (flipBob selected responses)).toReal := by
    have support : responses ∈ (bobLaw (menu.decodeProfile (PMF.pure nativeInitial)
        nativeHorizon scheduler players)).support := by
      rw [decoded]
      exact supported
    let control : app.Control := ⟨74, some bob, bobInput responses⟩
    obtain ⟨trace⟩ : Nonempty (arena.Trace (some control)) := bob_legal players responses support
    have observed := congrArg Prod.snd member.1
    dsimp only at observed
    obtain ⟨owner, associated, fixed⟩ :=
      true_view_handle control trace bob view observed member.2
    have hidden : publicGuess ((bobInput responses).observe app bob) = false := by
      rw [observed]
      exact uncertified
    obtain ⟨carolSame, related, sameInput⟩ :=
      bob_flip_facts players responses support selected owner associated fixed hidden
    refine ⟨⟨sameInput.trans member.1, related_true_false selected _ _ related member.2⟩, ?_⟩
    exact bob_flip_probability weight positive.le atMostOne selected owner responses
      (bob_true_response_different players responses support member.2) carolSame
  exact ENNReal.toReal_mono (outerMeasure_ne_top law _)
    (toOuterMeasure_le_of_injection law (event true) (event false) (flipBob selected)
      (fun _ _ _ _ same => (flipBob_involutive selected).injective same)
      (fun responses member supported => (moves responses member supported).1)
      (fun responses member supported => (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
        (PMF.apply_ne_top _ _)).mp (moves responses member supported).2))

end Vegas.Examples.SelectiveAssociation.Restricted.Prefix
