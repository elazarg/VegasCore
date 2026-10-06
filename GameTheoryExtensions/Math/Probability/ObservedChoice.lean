/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.ConditionalObservation
import GameTheoryExtensions.Math.Probability.Support

/-! # Choices drawn from an auxiliary observation

A hidden state is observed through a view and an auxiliary readout whose law
depends on the state only through the view. A phase run from each point then
produces a new readout and a choice. The phase law may depend on the point only
through the old readout, and the new readout determines both the old view and
the choice. Then the choice is a behavioral kernel of the old view alone (the
mixture of the phase over the conditional readout law), and the new readout
again depends on the new state only through its new view.

This is the one-step form of Kuhn's argument that private randomness which is
independent of the hidden state, given what a player knows, can be simulated by
that player.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- Disintegrating a readout law through a readout-determined choice. -/
private theorem map_readout_choice {Choice Readout Target : Type*} (law : PMF Readout)
    (choose : Readout → Choice) (target : Choice → Readout → Target) :
    law.map (fun readout => target (choose readout) readout) =
      (law.map choose).bind fun choice =>
        (fiberPosterior law choose choice).map (target choice) := by
  conv_lhs => rw [← fiberPosterior_reconstruct law choose]
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro choice chosen
  apply map_congr_on_support _
  intro readout member
  rw [fiberPosterior_support law choose choice chosen] at member
  rw [show choose readout = choice from member.1]

/-- **A choice drawn from an observation-local auxiliary readout is a
behavioral choice of the observation.** The phase law depends on the point
only through its readout; the new readout determines the old view and the
choice, which in turn determine the new view. The choice kernel is supported on
realized choices and, at unrealized views, on a given fallback. -/
theorem exists_observed_choice_factorization
    {Seed Source View Readout Final NextReadout Choice NextSource NextView Decoded : Type*}
    [Nonempty Choice]
    (prior : PMF Seed) (source : Seed → Source) (read : Seed → Readout)
    (view : Source → View) (noise : View → PMF Readout)
    (factor : prior.map (fun seed => (source seed, read seed)) =
      (prior.map source).bind fun config =>
        (noise (view config)).map fun extra => (config, extra))
    (phase : Seed → PMF Final) (out : Final → NextReadout)
    (coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      read left = read right → (phase left).map out = (phase right).map out)
    (advance : Source → Choice → NextSource) (nextView : NextSource → NextView)
    (decode : Seed → Final → Decoded) (embed : NextSource → Decoded)
    (decoded : ∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
      ∃ choice, decode seed final = embed (advance (source seed) choice))
    (determined : ∀ left ∈ prior.support, ∀ leftFinal ∈ (phase left).support,
      ∀ right ∈ prior.support, ∀ rightFinal ∈ (phase right).support,
      ∀ leftChoice rightChoice,
        decode left leftFinal = embed (advance (source left) leftChoice) →
        decode right rightFinal = embed (advance (source right) rightChoice) →
        out leftFinal = out rightFinal →
        nextView (advance (source left) leftChoice) =
          nextView (advance (source right) rightChoice))
    (reflects : ∀ left leftChoice right rightChoice,
      nextView (advance left leftChoice) = nextView (advance right rightChoice) →
        view left = view right ∧ leftChoice = rightChoice)
    (fallback : View → PMF Choice) :
    ∃ kernel : View → PMF Choice,
      (∀ observed choice, choice ∈ (kernel observed).support →
        choice ∈ (fallback observed).support ∨
          ∃ seed ∈ prior.support, ∃ final ∈ (phase seed).support,
            decode seed final = embed (advance (source seed) choice)) ∧
      ∃ nextNoise : NextView → PMF NextReadout,
        (prior.bind fun seed => (phase seed).map fun final => (decode seed final, out final)) =
          ((prior.map source).bind fun config =>
            (kernel (view config)).map (advance config)).bind fun next =>
              (nextNoise (nextView next)).map fun extra => (embed next, extra) := by
  classical
  -- The choice is a function of the new readout on realized points.
  let Realized := fun extra : NextReadout =>
    ∃ seed ∈ prior.support, ∃ final ∈ (phase seed).support, out final = extra
  let readChoice : NextReadout → Choice := fun extra =>
    if present : Realized extra then
      (decoded present.choose present.choose_spec.1 present.choose_spec.2.choose
        present.choose_spec.2.choose_spec.1).choose
    else Classical.arbitrary Choice
  have readChoice_spec : ∀ seed ∈ prior.support, ∀ final ∈ (phase seed).support,
      ∀ choice, decode seed final = embed (advance (source seed) choice) →
        readChoice (out final) = choice := by
    intro seed supported final reached choice same
    have present : Realized (out final) := ⟨seed, supported, final, reached, rfl⟩
    simp only [readChoice, dite_eq_left present]
    have witness := (decoded present.choose present.choose_spec.1 present.choose_spec.2.choose
      present.choose_spec.2.choose_spec.1).choose_spec
    have views := determined _ present.choose_spec.1 _ present.choose_spec.2.choose_spec.1
      seed supported final reached _ choice witness same
      present.choose_spec.2.choose_spec.2
    exact (reflects _ _ _ _ views).2
  -- The new readout depends on the state only through the old view.
  obtain ⟨readout, readoutLaw⟩ := exists_updated_observation_kernel_of_readout prior source read
    view noise factor (fun _ => PMF.pure Unit.unit) (fun config _ => config) view
    (fun seed _ => (phase seed).map out)
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same =>
      coupled left leftSupport right rightSupport same)
  have joint : (prior.bind fun seed => (phase seed).map fun final => (source seed, out final)) =
      (prior.map source).bind fun config =>
        (readout (view config)).map fun extra => (config, extra) := by
    simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, PMF.map_comp,
      Function.comp_def] using readoutLaw
  let realizedView := fun observed : View => ∃ seed ∈ prior.support, view (source seed) = observed
  let kernel := fun observed : View =>
    if realizedView observed then (readout observed).map readChoice else fallback observed
  let posterior := fun (observed : View) (choice : Choice) =>
    fiberPosterior (readout observed) readChoice choice
  let default : PMF NextReadout := prior.bind fun seed => (phase seed).map out
  let nextNoise := fun next : NextView =>
    if present : ∃ config choice, nextView (advance config choice) = next then
      posterior (view present.choose) present.choose_spec.choose
    else default
  have nextNoise_eq (config : Source) (choice : Choice) :
      nextNoise (nextView (advance config choice)) = posterior (view config) choice := by
    have present : ∃ other otherChoice,
        nextView (advance other otherChoice) = nextView (advance config choice) :=
      ⟨config, choice, rfl⟩
    simp only [nextNoise, dite_eq_left present]
    obtain ⟨views, choices⟩ := reflects _ _ _ _ present.choose_spec.choose_spec
    rw [views, choices]
  refine ⟨kernel, ?_, nextNoise, ?_⟩
  · intro observed choice member
    by_cases realized : realizedView observed
    · right
      simp only [kernel, ite_eq_left realized, PMF.support_map] at member
      obtain ⟨extra, extraSupport, rfl⟩ := member
      obtain ⟨start, startSupport, startView⟩ := realized
      have pair : (source start, extra) ∈ ((prior.map source).bind fun config =>
          (readout (view config)).map fun extra => (config, extra)).support := by
        rw [PMF.support_bind]
        refine Set.mem_iUnion₂.mpr ⟨source start, PMF.support_map .. ▸ ⟨start, startSupport, rfl⟩,
          ?_⟩
        rw [PMF.support_map]
        exact ⟨extra, by rwa [startView], rfl⟩
      rw [← joint, PMF.support_bind] at pair
      obtain ⟨seed, seedSupport, member⟩ := Set.mem_iUnion₂.mp pair
      obtain ⟨final, reached, same⟩ := PMF.support_map .. ▸ member
      obtain ⟨actual, decodedEq⟩ := decoded seed seedSupport final reached
      have chosen := readChoice_spec seed seedSupport final reached actual decodedEq
      rw [show out final = extra from (Prod.mk.inj same).2] at chosen
      rw [chosen]
      exact ⟨seed, seedSupport, final, reached, decodedEq⟩
    · left
      simpa only [kernel, ite_eq_right realized] using member
  · calc
      _ = (prior.bind fun seed => (phase seed).map fun final => (source seed, out final)).map
          fun pair => (embed (advance pair.1 (readChoice pair.2)), pair.2) := by
        rw [PMF.map_bind]
        apply bind_congr_on_support _
        intro seed supported
        rw [PMF.map_comp]
        apply map_congr_on_support _
        intro final reached
        obtain ⟨choice, decodedEq⟩ := decoded seed supported final reached
        have chosen := readChoice_spec seed supported final reached choice decodedEq
        simp only [Function.comp_apply, chosen, decodedEq]
      _ = (prior.map source).bind fun config =>
          (readout (view config)).map fun extra =>
            (embed (advance config (readChoice extra)), extra) := by
        rw [joint, PMF.map_bind]
        simp only [PMF.map_comp, Function.comp_def]
      _ = (prior.map source).bind fun config =>
          (kernel (view config)).bind fun choice =>
            (nextNoise (nextView (advance config choice))).map fun extra =>
              (embed (advance config choice), extra) := by
        apply bind_congr_on_support _
        intro config supported
        have realized : realizedView (view config) := by
          obtain ⟨seed, seedSupport, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨seed, seedSupport, rfl⟩
        simp only [kernel, ite_eq_left realized, nextNoise_eq]
        exact map_readout_choice (readout (view config)) readChoice
          (fun choice extra => (embed (advance config choice), extra))
      _ = _ := by
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]

end GameTheory.Math.Probability
