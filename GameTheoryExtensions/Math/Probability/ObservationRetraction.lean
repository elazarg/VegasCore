/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.ConditionalNoise

/-! # Conditioning an observation-local expansion and retraction

An expansion can restore hidden aliases of a source state. If its observation
law depends only on the source observation, conditioning the expanded state
and then retracting gives the original source posterior. Only supported
states and a positive observed fiber enter the argument.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {Source Native SourceInfo NativeInfo : Type*}

/-- Conditioning on an observation of a readout commutes with retaining that
readout. The positivity premise avoids the arbitrary empty-fiber fallback. -/
theorem map_conditional_readout {A B Info : Type*} (law : FinDist A)
    (read : A → B) (observe : B → Info) (observed : Info)
    (present : observed ∈ (law.map (observe ∘ read)).support) :
    (law.condOnFibre (observe ∘ read) observed).map read =
      (law.map read).condOnFibre observe observed := by
  classical
  obtain ⟨point, supported, equal⟩ := support_map .. ▸ present
  have originalMeets : ∃ a ∈ (observe ∘ read) ⁻¹' {observed}, a ∈ law.support :=
    ⟨point, equal, supported⟩
  have imageMeets : ∃ b ∈ observe ⁻¹' {observed}, b ∈ (law.map read).support := by
    refine ⟨read point, equal, ?_⟩
    rw [support_map]
    exact ⟨point, supported, rfl⟩
  rw [condOnFibre, dite_eq_left originalMeets, condOnFibre, dite_eq_left imageMeets]
  apply ext_of_prob
  intro value
  rw [prob_map_eq_probOf_preimage_singleton, probOf_condOn_eq_inter, prob_condOn,
    probOf_map]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  by_cases same : observe value = observed
  · rw [ite_eq_left same, prob_map_eq_probOf_preimage_singleton]
    congr 1
    apply probOf_congr
    intro a _
    change (observe (read a) = observed ∧ read a = value) ↔ read a = value
    exact ⟨And.right, fun equal => ⟨equal ▸ same, equal⟩⟩
  · rw [ite_eq_right same]
    have empty : (observe ∘ read) ⁻¹' {observed} ∩ read ⁻¹' {value} = ∅ := by
      ext a
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro matching projected
      exact same (projected ▸ matching)
    rw [empty]
    have zero : law.probOf (∅ : Set A) = 0 := by
      rw [← expect_indicator_eq_probOf]
      simp
    rw [zero, zero_div]

/-- Retraction after conditioning recovers the source posterior whenever the
expansion's observation law is constant on each supported source information
fiber. The expanded observation may contain additional random distinctions.
No independence between the source state and its prior is assumed. -/
theorem conditional_retraction (prior : FinDist Source)
    (kernel : Source → FinDist Native) (retract : Native → Source)
    (sourceObserve : Source → SourceInfo) (nativeObserve : Native → NativeInfo)
    (project : NativeInfo → SourceInfo)
    (commutes : ∀ a, sourceObserve (retract a) = project (nativeObserve a))
    (restores : ∀ s ∈ prior.support, ∀ a ∈ (kernel s).support, retract a = s)
    (locality : ∀ s ∈ prior.support, ∀ t ∈ prior.support,
      sourceObserve s = sourceObserve t →
        (kernel s).map nativeObserve = (kernel t).map nativeObserve)
    (observed : NativeInfo) (present : observed ∈ ((prior.bind kernel).map nativeObserve).support) :
    (((prior.bind kernel).condOnFibre nativeObserve observed).map retract) =
      prior.condOnFibre sourceObserve (project observed) := by
  classical
  let expanded := prior.bind kernel
  let read := fun a => (retract a, nativeObserve a)
  let information := fun pair : Source × NativeInfo => (sourceObserve pair.1, pair.2)
  let joint := prior.bind fun s =>
    ((kernel s).map nativeObserve).map fun signal => (s, signal)
  have jointLaw : expanded.map read = joint := by
    rw [map_bind]
    apply bind_congr
    intro s supported
    rw [map_comp]
    apply map_congr_of_eq_on_support
    intro a member
    exact Prod.ext (restores s supported a member) rfl
  obtain ⟨a, aSupport, aView⟩ := support_map .. ▸ present
  obtain ⟨s, sSupport, member⟩ := Set.mem_iUnion₂.mp (support_bind .. ▸ aSupport)
  have sourceView : sourceObserve s = project observed := by
    rw [← restores s sSupport a member, commutes, aView]
  have noisePresent : ∃ s ∈ prior.support,
      sourceObserve s = project observed ∧ observed ∈ ((kernel s).map nativeObserve).support := by
    refine ⟨s, sSupport, sourceView, ?_⟩
    rw [support_map]
    exact ⟨a, member, aView⟩
  have augmentedPresent : (project observed, observed) ∈
      (expanded.map (information ∘ read)).support := by
    rw [support_map]
    refine ⟨a, aSupport, ?_⟩
    exact Prod.ext ((commutes a).trans (congrArg project aView)) aView
  have sameFiber : (information ∘ read) ⁻¹' {(project observed, observed)} =
      nativeObserve ⁻¹' {observed} := by
    ext value
    change (sourceObserve (retract value), nativeObserve value) =
      (project observed, observed) ↔ nativeObserve value = observed
    rw [commutes]
    exact ⟨fun equal => (Prod.mk.inj equal).2,
      fun equal => Prod.ext (congrArg project equal) equal⟩
  have conditional : expanded.condOnFibre (information ∘ read) (project observed, observed) =
      expanded.condOnFibre nativeObserve observed := by
    unfold condOnFibre
    rw [sameFiber]
  have projected := map_conditional_readout expanded read information
    (project observed, observed) augmentedPresent
  rw [conditional, jointLaw] at projected
  have final := conditional_kernel_of_fiber prior sourceObserve
    (fun s => (kernel s).map nativeObserve) locality (project observed) observed noisePresent
  change ((joint.condOnFibre information (project observed, observed)).map Prod.fst) = _ at final
  rw [← projected, map_comp] at final
  exact final

/-- If a transition determines its new observation from the old state,
conditioning can be performed before that transition. All transition laws
remain unchanged; only the prior is conditioned. -/
theorem conditional_bind_of_observation {Info : Type*} (prior : FinDist Source)
    (kernel : Source → FinDist Native) (before : Source → Info) (after : Native → Info)
    (determines : ∀ s ∈ prior.support, ∀ a ∈ (kernel s).support, after a = before s)
    (observed : Info) (present : observed ∈ (prior.map before).support) :
    (prior.bind kernel).condOnFibre after observed =
      (prior.condOnFibre before observed).bind kernel := by
  classical
  have observations : (prior.bind kernel).map after = prior.map before := by
    rw [map_bind, map_eq_bind]
    apply bind_congr
    intro s supported
    calc
      (kernel s).map after = (kernel s).map (fun _ => before s) := by
        apply map_congr_of_eq_on_support
        exact determines s supported
      _ = FinDist.pure (before s) := map_const _ _
  obtain ⟨s, sSupported, sView⟩ := support_map .. ▸ present
  have oldMeets : ∃ s ∈ before ⁻¹' {observed}, s ∈ prior.support :=
    ⟨s, sView, sSupported⟩
  have newPresent : observed ∈ ((prior.bind kernel).map after).support := by
    rwa [observations]
  obtain ⟨a, aSupported, aView⟩ := support_map .. ▸ newPresent
  have newMeets : ∃ a ∈ after ⁻¹' {observed}, a ∈ (prior.bind kernel).support :=
    ⟨a, aView, aSupported⟩
  have mass : (prior.bind kernel).probOf (after ⁻¹' {observed}) =
      prior.probOf (before ⁻¹' {observed}) := by
    rw [← prob_map_eq_probOf_preimage_singleton, observations,
      prob_map_eq_probOf_preimage_singleton]
  rw [condOnFibre, dite_eq_left newMeets, condOnFibre, dite_eq_left oldMeets]
  apply ext_of_prob
  intro value
  rw [prob_condOn]
  simp only [prob_bind, Set.mem_preimage, Set.mem_singleton_iff]
  by_cases matched : after value = observed
  · rw [ite_eq_left matched, mass]
    symm
    apply expect_condOn_eq_div_of_eq_zero_off
    intro s supported mismatch
    apply prob_eq_zero_iff.mpr
    intro possible
    exact mismatch ((determines s supported value possible).symm.trans matched)
  · rw [ite_eq_right matched]
    symm
    calc
      _ = (prior.condOn (before ⁻¹' {observed}) oldMeets).expect (fun _ => 0) := by
        apply expect_congr
        intro s supported
        obtain ⟨sView, sSupported⟩ := support_condOn _ _ _ supported
        apply prob_eq_zero_iff.mpr
        intro possible
        exact matched ((determines s sSupported value possible).trans sView)
      _ = 0 := expect_const _ _

/-- Once the finer observation is made, an earlier observation determined by
it does not further change the posterior. The support condition also handles
the total conditioning operator's unused empty-fiber fallback. -/
theorem conditional_fiber_after_projection {A Info Coarse : Type*} (law : FinDist A)
    (observe : A → Info) (project : Info → Coarse) (coarse : Coarse) (observed : Info)
    (present : observed ∈ ((law.condOnFibre (project ∘ observe) coarse).map observe).support) :
    (law.condOnFibre (project ∘ observe) coarse).condOnFibre observe observed =
      law.condOnFibre observe observed := by
  classical
  by_cases coarseMeets : ∃ a ∈ (project ∘ observe) ⁻¹' {coarse}, a ∈ law.support
  · have coarseLaw : law.condOnFibre (project ∘ observe) coarse =
        law.condOn ((project ∘ observe) ⁻¹' {coarse}) coarseMeets := by
      rw [condOnFibre, dite_eq_left coarseMeets]
    rw [coarseLaw] at present ⊢
    obtain ⟨a, aSupported, aView⟩ := support_map .. ▸ present
    have aOriginal := (support_condOn _ _ _ aSupported).2
    have aCoarse := (support_condOn _ _ _ aSupported).1
    have projected : project observed = coarse := by
      change project (observe a) = coarse at aCoarse
      rwa [aView] at aCoarse
    have fineMeets : ∃ a ∈ observe ⁻¹' {observed}, a ∈ law.support :=
      ⟨a, aView, aOriginal⟩
    have nestedMeets : ∃ a ∈ observe ⁻¹' {observed},
        a ∈ (law.condOn ((project ∘ observe) ⁻¹' {coarse}) coarseMeets).support :=
      ⟨a, aView, aSupported⟩
    rw [condOnFibre, dite_eq_left nestedMeets, condOnFibre, dite_eq_left fineMeets]
    apply condOn_condOn law coarseMeets fineMeets
    intro value member
    change project (observe value) = coarse
    rw [show observe value = observed from member.1, projected]
  · have coarseLaw : law.condOnFibre (project ∘ observe) coarse = law := by
      rw [condOnFibre, dite_eq_right coarseMeets]
    rw [coarseLaw]

end GameTheory.Math.Probability.FinDist
