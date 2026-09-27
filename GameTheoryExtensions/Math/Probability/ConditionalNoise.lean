/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # Auxiliary observations conditional on an existing observation

An extra finite channel whose law depends only on an existing observation does
not change the posterior of the underlying state. Positive joint observations
are explicit; this is the finite Bayes calculation used at perturbations, not
an assertion about arbitrary off-path beliefs.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {State Observation Noise : Type*}

theorem conditional_observation_kernel (prior : FinDist State)
    (observe : State → Observation) (noise : Observation → FinDist Noise)
    (observed : Observation) (extra : Noise)
    (present : observed ∈ (prior.map observe).support)
    (possible : extra ∈ (noise observed).support) :
    let joint := prior.bind fun state =>
      (noise (observe state)).map fun signal => (state, signal)
    (joint.condOnFibre (fun pair => (observe pair.1, pair.2)) (observed, extra)).map
      Prod.fst = prior.condOnFibre observe observed := by
  classical
  dsimp only
  let joint := prior.bind fun state =>
    (noise (observe state)).map fun signal => (state, signal)
  let information := fun pair : State × Noise => (observe pair.1, pair.2)
  obtain ⟨witness, supported, equal⟩ := support_map .. ▸ present
  have oldMeets : ∃ state ∈ observe ⁻¹' {observed}, state ∈ prior.support :=
    ⟨witness, equal, supported⟩
  have meets : ∃ pair ∈ information ⁻¹' {(observed, extra)}, pair ∈ joint.support := by
    refine ⟨(witness, extra), ?_, ?_⟩
    · exact Prod.ext equal rfl
    · simp only [joint, support_bind, Set.mem_iUnion]
      refine ⟨witness, supported, ?_⟩
      rw [support_map]
      exact ⟨extra, by simpa only [equal] using possible, rfl⟩
  have mapped : joint.map information =
      (prior.map observe).bind fun observation =>
        (noise observation).map fun signal => (observation, signal) := by
    simp only [joint, information, map_bind, map_comp, bind_map, Function.comp_def]
  have mass : joint.probOf (information ⁻¹' {(observed, extra)}) =
      (prior.map observe).prob observed * (noise observed).prob extra := by
    rw [← prob_map_eq_probOf_preimage_singleton, mapped, prob_bind_map_prod]
  have noisePositive : 0 < (noise observed).prob extra := prob_pos_iff.mpr possible
  have conditional : joint.condOnFibre information (observed, extra) =
      (prior.condOnFibre observe observed).map (fun state => (state, extra)) := by
    rw [condOnFibre, dite_eq_left meets, condOnFibre, dite_eq_left oldMeets]
    apply ext_of_prob
    rintro ⟨state, signal⟩
    rw [prob_condOn, mass]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, information, Prod.mk.injEq]
    by_cases signalEq : signal = extra
    · subst signal
      rw [prob_map_of_injective (fun state => (state, extra))
        (fun _ _ same => (Prod.mk.inj same).1), prob_condOn]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases same : observe state = observed
      · rw [ite_eq_left ⟨same, True.intro⟩, ite_eq_left same]
        rw [show joint.prob (state, extra) =
          prior.prob state * (noise (observe state)).prob extra from
            prob_bind_map_prod prior (fun state => noise (observe state)) state extra]
        rw [same, ← prob_map_eq_probOf_preimage_singleton]
        exact mul_div_mul_right _ _ (ne_of_gt noisePositive)
      · rw [ite_eq_right (fun h => same h.1), ite_eq_right same]
    · rw [ite_eq_right (fun h => signalEq h.2)]
      symm
      apply prob_eq_zero_iff.mpr
      intro member
      obtain ⟨old, _, same⟩ := support_map .. ▸ member
      exact signalEq (congrArg Prod.snd same).symm
  change (joint.condOnFibre information (observed, extra)).map Prod.fst = _
  rw [conditional, map_comp]
  exact map_id _

/-- The same calculation needs channel equality only on supported states in
each original information fiber. No global factorization is supplied as a
premise: it is constructed from those finite supported fibers. -/
theorem conditional_kernel_of_fiber (prior : FinDist State)
    (observe : State → Observation) (kernel : State → FinDist Noise)
    (same : ∀ left ∈ prior.support, ∀ right ∈ prior.support,
      observe left = observe right → kernel left = kernel right)
    (observed : Observation) (extra : Noise)
    (present : ∃ state ∈ prior.support,
      observe state = observed ∧ extra ∈ (kernel state).support) :
    let joint := prior.bind fun state =>
      (kernel state).map fun signal => (state, signal)
    (joint.condOnFibre (fun pair => (observe pair.1, pair.2)) (observed, extra)).map
      Prod.fst = prior.condOnFibre observe observed := by
  classical
  let noise := fun observed =>
    if existsState : ∃ state ∈ prior.support, observe state = observed then
      kernel existsState.choose
    else kernel prior.support_nonempty.choose
  have factors (state : State) (supported : state ∈ prior.support) :
      kernel state = noise (observe state) := by
    have existsState : ∃ other ∈ prior.support, observe other = observe state :=
      ⟨state, supported, rfl⟩
    simp only [noise, dite_eq_left existsState]
    exact same state supported existsState.choose existsState.choose_spec.1
      existsState.choose_spec.2.symm
  have joint : (prior.bind fun state => (kernel state).map fun signal => (state, signal)) =
      prior.bind fun state => (noise (observe state)).map fun signal => (state, signal) := by
    apply bind_congr
    intro state supported
    rw [factors state supported]
  obtain ⟨state, supported, equal, possible⟩ := present
  have oldPresent : observed ∈ (prior.map observe).support := by
    rw [support_map]
    exact ⟨state, supported, equal⟩
  have noisePresent : extra ∈ (noise observed).support := by
    rw [← equal, ← factors state supported]
    exact possible
  dsimp only
  rw [joint]
  exact conditional_observation_kernel prior observe noise observed extra oldPresent noisePresent

end GameTheory.Math.Probability.FinDist
