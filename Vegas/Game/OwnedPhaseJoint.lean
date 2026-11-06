/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.ConditionalObservation
import GameTheoryExtensions.Math.Probability.ObservedChoice

/-! # The joint law of a phase one observer decides

A coupled prior pairs a hidden key with an observer's traffic, and the traffic
is noise read from the observer's view of the key. A phase replaces the traffic
by a law that depends only on the starting traffic. Then the joint law of the
key and the final traffic is the key law with a channel read from the view.
When the observer's choice is read from the final traffic and advances the key,
and the next view of the advanced key determines the previous view and, for an
active observer, the choice, the final traffic is again noise read from the
next view.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability

/-- **The joint law of an observer's phase.** -/
theorem exists_owned_phase_joint {Seed Key Traffic View Choice Next NextView : Type}
    (prior : PMF Seed) (key : Seed → Key) (start : Seed → Traffic) (view : Key → View)
    (noise : View → PMF Traffic)
    (factor : prior.map (fun seed => (key seed, start seed)) =
      (prior.map key).bind fun current =>
        (noise (view current)).map fun extra => (current, extra))
    (phase : Seed → PMF Traffic)
    (coupled : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      start left = start right → phase left = phase right)
    (pick : Traffic → Choice) (advance : Key → Choice → Next) (nextView : Next → NextView)
    (active : View → Prop)
    (reflects : ∀ left ∈ (prior.map key).support, ∀ right ∈ (prior.map key).support,
      ∀ leftChoice rightChoice,
      nextView (advance left leftChoice) = nextView (advance right rightChoice) →
        view left = view right)
    (remembered : ∀ left ∈ (prior.map key).support, ∀ right ∈ (prior.map key).support,
      ∀ leftChoice rightChoice, active (view left) →
      nextView (advance left leftChoice) = nextView (advance right rightChoice) →
        leftChoice = rightChoice)
    (automatic : ∀ current, ¬ active (view current) →
      ∀ first second, advance current first = advance current second) :
    ∃ channel : View → PMF Traffic, ∃ nextNoise : NextView → PMF Traffic,
      (prior.bind fun seed => (phase seed).map fun extra => (key seed, extra)) =
        (prior.map key).bind (fun current =>
          (channel (view current)).map fun extra => (current, extra)) ∧
      (prior.bind fun seed => (phase seed).map fun extra =>
          (advance (key seed) (pick extra), extra)) =
        ((prior.map key).bind fun current =>
          (channel (view current)).map fun extra => advance current (pick extra)).bind
          fun next => (nextNoise (nextView next)).map fun extra => (next, extra) := by
  classical
  obtain ⟨channel, channelLaw⟩ := exists_updated_observation_kernel_of_readout prior key start
    view noise factor (fun _ => PMF.pure ()) (fun current _ => current) view
    (fun seed _ => phase seed)
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right rightSupport _ _ _ same =>
      coupled left leftSupport right rightSupport same)
  have joint : (prior.bind fun seed => (phase seed).map fun extra => (key seed, extra)) =
      (prior.map key).bind fun current =>
        (channel (view current)).map fun extra => (current, extra) := by
    simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure] using channelLaw
  let nextNoise := fun next : NextView =>
    if present : ∃ current ∈ (prior.map key).support, ∃ choice,
        nextView (advance current choice) = next then
      if active (view present.choose) then
        fiberPosterior (channel (view present.choose)) pick present.choose_spec.2.choose
      else channel (view present.choose)
    else channel (view (prior.map key).support_nonempty.choose)
  refine ⟨channel, nextNoise, joint, ?_⟩
  have reread : (prior.bind fun seed => (phase seed).map fun extra =>
      (advance (key seed) (pick extra), extra)) =
      (prior.bind fun seed => (phase seed).map fun extra => (key seed, extra)).map
        (fun pair => (advance pair.1 (pick pair.2), pair.2)) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [reread, joint, PMF.map_bind, PMF.bind_bind]
  apply bind_congr_on_support _
  intro current supported
  have found (choice : Choice) : ∃ other ∈ (prior.map key).support, ∃ chosen,
      nextView (advance other chosen) = nextView (advance current choice) :=
    ⟨current, supported, choice, rfl⟩
  have noiseAt (choice : Choice) :
      nextNoise (nextView (advance current choice)) =
        if active (view current) then fiberPosterior (channel (view current)) pick choice
        else channel (view current) := by
    have present := found choice
    simp only [nextNoise, dite_eq_left present]
    have sameView := reflects _ present.choose_spec.1 current supported _ choice
      present.choose_spec.2.choose_spec
    by_cases live : active (view current)
    · have liveChosen : active (view present.choose) := sameView ▸ live
      rw [ite_eq_left liveChosen, ite_eq_left live, sameView]
      rw [remembered _ present.choose_spec.1 current supported _ choice liveChosen
        present.choose_spec.2.choose_spec]
    · have idleChosen : ¬ active (view present.choose) := sameView ▸ live
      rw [ite_eq_right idleChosen, ite_eq_right live, sameView]
  rw [PMF.map_comp, PMF.bind_map]
  change (channel (view current)).map (fun extra => (advance current (pick extra), extra)) = _
  by_cases live : active (view current)
  · rw [map_readout_choice (channel (view current)) pick
      (fun chosen extra => (advance current chosen, extra)), PMF.bind_map]
    apply bind_congr_on_support _
    intro extra _
    simp only [Function.comp_apply, noiseAt, live, ite_true]
  · have constant (extra : Traffic) : nextNoise (nextView (advance current (pick extra))) =
        channel (view current) := by
      rw [noiseAt, ite_eq_right live]
    obtain ⟨anchor, _⟩ := (channel (view current)).support_nonempty
    have fixed (extra : Traffic) : advance current (pick extra) =
        advance current (pick anchor) := automatic current live _ _
    simp only [Function.comp_def, constant, fixed]
    rw [PMF.bind_const]

end Vegas
