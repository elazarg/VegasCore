/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourcePrefixSymmetry
import VegasTests.SelectiveAssociationSourcePublishedEvidence
import GameTheoryExtensions.Math.Probability.ConditionalSymmetry
import Interaction.ReactiveAssessmentDecoding

/-! # Conditional hidden-bit fairness in the source response prefixes

These finite distributions sample the actual response prefixes. Earlier
responses and Carol's response are arbitrary information-local policies. Only
Alice's fresh binding response needs the checked hidden-bit symmetry. The
permutation fixes certified branches and swaps the uncertified hidden bit.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

def chooseAt {Claim : Type} (players : Player → (application Claim).Policy)
    (who : Player) (execution : (application Claim).Execution) :
    FinDist (application Claim).Action :=
  players who (execution.recall who) (execution.observe (application Claim) who)

structure BindingSample (Claim : Type) where
  first : (application Claim).Action
  second : (application Claim).Action
  binding : (application Claim).Action

def BindingSample.flip {Claim : Type} (sample : BindingSample Claim) : BindingSample Claim :=
  { sample with binding := flipResponse sample.binding }

theorem BindingSample.flip_involutive {Claim : Type} :
    Function.Involutive (BindingSample.flip (Claim := Claim)) := by
  rintro ⟨first, second, binding⟩
  simp only [flip]
  rw [flipResponse_involutive binding]

def BindingSample.Uncertified {Claim : Type} (sample : BindingSample Claim) : Prop :=
  bindingCertificates sample.first sample.second sample.binding = ∅

theorem BindingSample.uncertified_flip {Claim : Type} (sample : BindingSample Claim) :
    sample.flip.Uncertified ↔ sample.Uncertified :=
  bindingCertificates_flip_empty_iff sample.first sample.second sample.binding

open Classical in
def BindingSample.swapHidden {Claim : Type} (sample : BindingSample Claim) : BindingSample Claim :=
  if sample.Uncertified then sample.flip else sample

theorem BindingSample.swapHidden_involutive {Claim : Type} :
    Function.Involutive (BindingSample.swapHidden (Claim := Claim)) := by
  intro sample
  by_cases clean : sample.Uncertified
  · simp only [swapHidden, clean, ↓reduceIte, uncertified_flip]
    exact flip_involutive sample
  · simp only [swapHidden, clean, ↓reduceIte]

theorem BindingSample.uncertified_swapHidden {Claim : Type} (sample : BindingSample Claim) :
    sample.swapHidden.Uncertified ↔ sample.Uncertified := by
  unfold swapHidden
  split
  · exact sample.uncertified_flip
  · rfl

def bindingLaw {Claim : Type} (players : Player → (application Claim).Policy) :
    FinDist (BindingSample Claim) :=
  (chooseAt players alice (effect (root Claim) (.activate alice))).bind fun first =>
    (chooseAt players bob (effect (firstResponse first) (.activate bob))).bind fun second =>
      (chooseAt players alice (aliceInput first second)).map fun binding =>
        ⟨first, second, binding⟩

theorem bindingLaw_flip {Claim : Type} (players : Player → (application Claim).Policy)
    (symmetric : ∀ first second,
      (chooseAt players alice (aliceInput first second)).map flipResponse =
        chooseAt players alice (aliceInput first second)) :
    (bindingLaw players).map BindingSample.flip = bindingLaw players := by
  simp only [bindingLaw, FinDist.map_bind]
  apply FinDist.bind_congr
  intro first _
  apply FinDist.bind_congr
  intro second _
  rw [FinDist.map_comp]
  calc
    _ = ((chooseAt players alice (aliceInput first second)).map flipResponse).map
        (fun binding => BindingSample.mk first second binding) := by
      rw [FinDist.map_comp]
      rfl
    _ = _ := by rw [symmetric]

theorem bindingLaw_swapHidden {Claim : Type} (players : Player → (application Claim).Policy)
    (symmetric : ∀ first second,
      (chooseAt players alice (aliceInput first second)).map flipResponse =
        chooseAt players alice (aliceInput first second)) :
    (bindingLaw players).map BindingSample.swapHidden = bindingLaw players := by
  classical
  apply FinDist.ext_of_prob
  intro sample
  have mapped := FinDist.prob_map_of_injective BindingSample.swapHidden
    BindingSample.swapHidden_involutive.injective (bindingLaw players) sample.swapHidden
  rw [BindingSample.swapHidden_involutive] at mapped
  rw [mapped]
  by_cases clean : sample.Uncertified
  · rw [BindingSample.swapHidden, ite_eq_left clean]
    exact FinDist.prob_involution (bindingLaw players) BindingSample.flip
      BindingSample.flip_involutive (bindingLaw_flip players symmetric) sample
  · rw [BindingSample.swapHidden, ite_eq_right clean]

def BindingSample.carolInformation {Claim : Type} (sample : BindingSample Claim) :
    List (application Claim).PlayerEntry × (application Claim).PlayerView :=
  let execution := carolInput sample.first sample.second sample.binding
  (execution.recall carol, execution.observe (application Claim) carol)

theorem BindingSample.carolInformation_swapHidden {Claim : Type} (sample : BindingSample Claim) :
    sample.swapHidden.carolInformation = sample.carolInformation := by
  by_cases clean : sample.Uncertified
  · simp only [swapHidden, clean, ↓reduceIte]
    exact carolInput_information_flip sample.first sample.second sample.binding clean
  · rw [swapHidden, ite_eq_right clean]

open Classical in
def BindingSample.hiddenCarolInformation {Claim : Type} (sample : BindingSample Claim) :
    Option (List (application Claim).PlayerEntry × (application Claim).PlayerView) :=
  if sample.Uncertified then some sample.carolInformation else none

theorem BindingSample.hiddenCarolInformation_swapHidden {Claim : Type}
    (sample : BindingSample Claim) :
    sample.swapHidden.hiddenCarolInformation = sample.hiddenCarolInformation := by
  unfold hiddenCarolInformation
  rw [propext sample.uncertified_swapHidden, sample.carolInformation_swapHidden]

def BindingSample.value {Claim : Type} (sample : BindingSample Claim) : PublicationResult Bool :=
  selectedBinding 0 sample.binding

theorem BindingSample.value_swapHidden {Claim : Type} (sample : BindingSample Claim)
    (clean : sample.Uncertified) : sample.swapHidden.value = flipBinding sample.value := by
  simp only [swapHidden, clean, ↓reduceIte, value, flip]
  exact selectedBinding_flip 0 sample.binding

theorem carol_conditional_fair {Claim : Type} (players : Player → (application Claim).Policy)
    (symmetric : ∀ first second,
      (chooseAt players alice (aliceInput first second)).map flipResponse =
        chooseAt players alice (aliceInput first second))
    (info : List (application Claim).PlayerEntry × (application Claim).PlayerView)
    (positive : ∃ sample ∈ {sample | BindingSample.hiddenCarolInformation sample = some info},
      sample ∈ (bindingLaw players).support) :
    ((bindingLaw players).condOn
      {sample | BindingSample.hiddenCarolInformation sample = some info} positive).probOf
        {sample | sample.Uncertified ∧ sample.value = .success false} =
    ((bindingLaw players).condOn
      {sample | BindingSample.hiddenCarolInformation sample = some info} positive).probOf
        {sample | sample.Uncertified ∧ sample.value = .success true} := by
  apply FinDist.condOn_observation_probOf_eq _ BindingSample.swapHidden
    BindingSample.swapHidden_involutive (bindingLaw_swapHidden players symmetric)
    BindingSample.hiddenCarolInformation BindingSample.hiddenCarolInformation_swapHidden
  intro sample _
  change sample.swapHidden.Uncertified ∧ sample.swapHidden.value = .success false ↔
    sample.Uncertified ∧ sample.value = .success true
  rw [sample.uncertified_swapHidden]
  by_cases clean : sample.Uncertified
  · rw [sample.value_swapHidden clean]
    simp only [clean, true_and, flipBinding_success, Bool.not_false]
  · simp only [clean, false_and]

abbrev GuessSample (Claim : Type) := BindingSample Claim × (application Claim).Action

def swapGuess {Claim : Type} (sample : GuessSample Claim) : GuessSample Claim :=
  (sample.1.swapHidden, sample.2)

theorem swapGuess_involutive {Claim : Type} :
    Function.Involutive (swapGuess (Claim := Claim)) := by
  rintro ⟨sample, guess⟩
  change (sample.swapHidden.swapHidden, guess) = (sample, guess)
  rw [BindingSample.swapHidden_involutive sample]

def guessLaw {Claim : Type} (players : Player → (application Claim).Policy) :
    FinDist (GuessSample Claim) :=
  (bindingLaw players).bind fun sample =>
    (players carol sample.carolInformation.1 sample.carolInformation.2).map fun guess =>
      (sample, guess)

theorem guessLaw_swap {Claim : Type} (players : Player → (application Claim).Policy)
    (symmetric : ∀ first second,
      (chooseAt players alice (aliceInput first second)).map flipResponse =
        chooseAt players alice (aliceInput first second)) :
    (guessLaw players).map swapGuess = guessLaw players := by
  rw [guessLaw, FinDist.map_bind]
  calc
    _ = ((bindingLaw players).map BindingSample.swapHidden).bind (fun sample =>
        (players carol sample.carolInformation.1 sample.carolInformation.2).map fun guess =>
          (sample, guess)) := by
      rw [FinDist.bind_map]
      apply FinDist.bind_congr
      intro sample _
      rw [sample.carolInformation_swapHidden, FinDist.map_comp]
      rfl
    _ = _ := by rw [bindingLaw_swapHidden players symmetric]

def bobInformation {Claim : Type} (sample : GuessSample Claim) :
    List (application Claim).PlayerEntry × (application Claim).PlayerView :=
  let execution := bobInput sample.1.first sample.1.second sample.1.binding sample.2
  (execution.recall bob, execution.observe (application Claim) bob)

theorem bobInformation_swap {Claim : Type} (sample : GuessSample Claim) :
    bobInformation (swapGuess sample) = bobInformation sample := by
  rcases sample with ⟨sample, guess⟩
  change bobInformation (sample.swapHidden, guess) = bobInformation (sample, guess)
  by_cases clean : sample.Uncertified
  · rw [BindingSample.swapHidden, ite_eq_left clean]
    exact bobInput_information_flip sample.first sample.second sample.binding guess clean
  · rw [BindingSample.swapHidden, ite_eq_right clean]

open Classical in
def hiddenBobInformation {Claim : Type} (sample : GuessSample Claim) :
    Option (List (application Claim).PlayerEntry × (application Claim).PlayerView) :=
  if sample.1.Uncertified then some (bobInformation sample) else none

theorem hiddenBobInformation_swap {Claim : Type} (sample : GuessSample Claim) :
    hiddenBobInformation (swapGuess sample) = hiddenBobInformation sample := by
  classical
  unfold hiddenBobInformation
  change (if sample.1.swapHidden.Uncertified then some (bobInformation (swapGuess sample))
    else none) = _
  rw [propext sample.1.uncertified_swapHidden, bobInformation_swap]

theorem bob_conditional_fair {Claim : Type} (players : Player → (application Claim).Policy)
    (symmetric : ∀ first second,
      (chooseAt players alice (aliceInput first second)).map flipResponse =
        chooseAt players alice (aliceInput first second))
    (info : List (application Claim).PlayerEntry × (application Claim).PlayerView)
    (positive : ∃ sample ∈ {sample | hiddenBobInformation sample = some info},
      sample ∈ (guessLaw players).support) :
    ((guessLaw players).condOn {sample | hiddenBobInformation sample = some info} positive).probOf
        {sample | sample.1.Uncertified ∧ sample.1.value = .success false} =
    ((guessLaw players).condOn {sample | hiddenBobInformation sample = some info} positive).probOf
        {sample | sample.1.Uncertified ∧ sample.1.value = .success true} := by
  apply FinDist.condOn_observation_probOf_eq _ swapGuess swapGuess_involutive
    (guessLaw_swap players symmetric) hiddenBobInformation hiddenBobInformation_swap
  intro sample _
  change sample.1.swapHidden.Uncertified ∧ sample.1.swapHidden.value = .success false ↔
    sample.1.Uncertified ∧ sample.1.value = .success true
  rw [sample.1.uncertified_swapHidden]
  by_cases clean : sample.1.Uncertified
  · rw [sample.1.value_swapHidden clean]
    simp only [clean, true_and, flipBinding_success, Bool.not_false]
  · simp only [clean, false_and]

theorem decode_profile (Claim : Type) [Fintype Claim] (defaultClaim : Claim) (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView) :
    (menu Claim).decodeProfile (FinDist.pure initial) horizon (scheduler Claim)
      (profile Claim defaultClaim) who past view = policy Claim defaultClaim who past view := by
  change ((menu Claim).embedPolicy (FinDist.pure initial) horizon (scheduler Claim) who
    ((menu Claim).restrictPolicy (FinDist.pure initial) horizon (scheduler Claim) who
      (policy Claim defaultClaim who) _) (some (past, view))).map _ = _
  rw [(menu Claim).embed_restrictPolicy (FinDist.pure initial) horizon (scheduler Claim) who
    (policy Claim defaultClaim who) _ past view (policy_covered Claim defaultClaim who past view)]
  change (application Claim).decodePolicy
    ((application Claim).encodePolicy (policy Claim defaultClaim who)) past view = _
  rw [ReactiveApplication.decode_encodePolicy]

def tremblePlayers (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) :
    Player → (application Claim).Policy :=
  (menu Claim).decodeProfile (FinDist.pure initial) horizon (scheduler Claim)
    (tremble Claim defaultClaim weight positive atMostOne).strategy

theorem tremblePlayers_mixture (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1) (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView) :
    tremblePlayers Claim defaultClaim weight positive atMostOne who past view =
      FinDist.mix weight positive.le atMostOne ((menu Claim).uniformResponses who past view)
        (policy Claim defaultClaim who past view) := by
  rw [tremblePlayers, tremble, ReactiveApplication.ResponseMenu.decode_perturbedAssessment,
    decode_profile]

theorem tremble_alice_symmetric (Claim : Type) [Fintype Claim] (defaultClaim : Claim)
    (weight : ℝ) (positive : 0 < weight) (atMostOne : weight ≤ 1)
    (first second : (application Claim).Action) :
    (chooseAt (tremblePlayers Claim defaultClaim weight positive atMostOne) alice
      (aliceInput first second)).map flipResponse =
    chooseAt (tremblePlayers Claim defaultClaim weight positive atMostOne) alice
      (aliceInput first second) := by
  unfold chooseAt
  rw [tremblePlayers_mixture, FinDist.map_mix, uniform_flip,
    alice_policy_flip Claim defaultClaim _ _ (aliceInput_visit first second)]

theorem carol_joint_fair {Claim : Type} (players : Player → (application Claim).Policy)
    (symmetric : ∀ first second,
      (chooseAt players alice (aliceInput first second)).map flipResponse =
        chooseAt players alice (aliceInput first second))
    (info : List (application Claim).PlayerEntry × (application Claim).PlayerView)
    (hidden : NoPublicAlice info.2) :
    (bindingLaw players).probOf
        {sample | sample.carolInformation = info ∧ sample.value = .success false} =
      (bindingLaw players).probOf
        {sample | sample.carolInformation = info ∧ sample.value = .success true} := by
  apply FinDist.probOf_eq_of_involution _ BindingSample.swapHidden
    (bindingLaw_swapHidden players symmetric)
  intro sample _
  change sample.swapHidden.carolInformation = info ∧ sample.swapHidden.value = .success false ↔
    sample.carolInformation = info ∧ sample.value = .success true
  rw [sample.carolInformation_swapHidden]
  by_cases same : sample.carolInformation = info
  · have clean : sample.Uncertified :=
      carol_no_public_uncertified sample.first sample.second sample.binding (by
        change NoPublicAlice sample.carolInformation.2
        rw [same]
        exact hidden)
    rw [sample.value_swapHidden clean]
    simp only [same, true_and, flipBinding_success, Bool.not_false]
  · simp only [same, false_and]

theorem bob_joint_fair {Claim : Type} (players : Player → (application Claim).Policy)
    (symmetric : ∀ first second,
      (chooseAt players alice (aliceInput first second)).map flipResponse =
        chooseAt players alice (aliceInput first second))
    (info : List (application Claim).PlayerEntry × (application Claim).PlayerView)
    (hidden : NoPublicAlice info.2) :
    (guessLaw players).probOf
        {sample | bobInformation sample = info ∧ sample.1.value = .success false} =
      (guessLaw players).probOf
        {sample | bobInformation sample = info ∧ sample.1.value = .success true} := by
  apply FinDist.probOf_eq_of_involution _ swapGuess (guessLaw_swap players symmetric)
  intro sample _
  change bobInformation (swapGuess sample) = info ∧ sample.1.swapHidden.value = .success false ↔
    bobInformation sample = info ∧ sample.1.value = .success true
  rw [bobInformation_swap]
  by_cases same : bobInformation sample = info
  · have clean : sample.1.Uncertified :=
      bob_no_public_uncertified sample.1.first sample.1.second sample.1.binding sample.2 (by
        change NoPublicAlice (bobInformation sample).2
        rw [same]
        exact hidden)
    rw [sample.1.value_swapHidden clean]
    simp only [same, true_and, flipBinding_success, Bool.not_false]
  · simp only [same, false_and]

end VegasTests.SelectiveAssociation.NamedSource
